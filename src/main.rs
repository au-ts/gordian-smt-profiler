use anyhow;
use anyhow::Error;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::io::BufRead;

use z3tracer::{
    model::QuantCost,
    syntax::{MatchedTerm, QiFrame, QiKey},
    Model, ModelConfig,
};

use eframe::{run_native, App, CreationContext};
use egui;
use egui::{
    Context,
    epaint::TextShape, FontFamily, FontId, Rect, Rounding,Shape, Stroke, Vec2
};

use egui_graphs::{Graph, GraphView, SettingsInteraction};
use petgraph::{stable_graph::StableGraph, Directed};

use clap::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(short, long)]
    file: std::path::PathBuf,

    #[arg(short, long)]
    gui: bool,
}

fn process_file(path: &std::path::Path) -> anyhow::Result<Model> {
    let file = std::io::BufReader::new(std::fs::File::open(path)?);
    let line_count = file.lines().count();
    let file = std::io::BufReader::new(std::fs::File::open(path)?);

    let mut model_config = ModelConfig::default();
    model_config.parser_config.skip_z3_version_check = true;
    model_config.parser_config.ignore_invalid_lines = true;
    model_config.parser_config.show_progress_bar = true;
    model_config.skip_log_consistency_checks = true;
    model_config.log_term_equalities = false;
    model_config.log_internal_term_equalities = false;

    let mut model = Model::new(model_config);

    let e = Error::new(std::io::Error::new(
        std::io::ErrorKind::InvalidInput,
        "Invalid path",
    ));

    let p: Option<String> = match path.to_str() {
        Some(pa) => Some(pa.to_owned()),
        None => return Err(e),
    };

    model.process(p, file, line_count)?;
    Ok(model)
}

#[derive(Debug)]
pub struct InstantiationGraph {
    pub edges: HashMap<(u64, usize), HashSet<(u64, usize)>>,
    pub names: HashMap<(u64, usize), String>,
    pub nodes: HashSet<(u64, usize)>,
}

#[derive(Debug)]
pub struct Profiler {
    quantifier_stats: Vec<QuantCost>,
    instantiation_graph: InstantiationGraph,
}

impl Profiler {
    pub fn parse(filename: &std::path::Path) -> anyhow::Result<Self> {
        let model = process_file(filename)?;

        let graph = Self::make_instantiation_graph(&model);

        let quant_costs = model.quant_costs();
        let mut user_quant_costs = quant_costs.into_iter().collect::<Vec<_>>();
        user_quant_costs.sort_by_key(|v| v.instantiations * v.cost);
        user_quant_costs.reverse();

        Ok(Profiler {
            quantifier_stats: user_quant_costs,
            instantiation_graph: graph,
        })
    }

    fn make_instantiation_graph(model: &Model) -> InstantiationGraph {
        let quantifier_inst_matches =
            model
                .instantiations()
                .iter()
                .filter(|(_, quant_inst)| match quant_inst.frame {
                    QiFrame::Discovered { .. } => false,
                    QiFrame::NewMatch { .. } => true,
                });

        // Track which instantiations caused which enodes to appear
        let mut term_blame = HashMap::new();
        for (qi_key, quant_inst) in quantifier_inst_matches.clone() {
            for inst in &quant_inst.instances {
                for node_ident in &inst.enodes {
                    term_blame.insert(node_ident, qi_key);
                }
            }
        }

        // Create a graph over QuantifierInstances,
        // where U->V if U produced an e-term that
        // triggered V
        let mut graph: BTreeMap<QiKey, BTreeSet<QiKey>> = BTreeMap::new();
        for (qi_key, _) in quantifier_inst_matches.clone() {
            graph.insert(*qi_key, BTreeSet::new());
        }
        for (qi_key, quant_inst) in quantifier_inst_matches.clone() {
            match &quant_inst.frame {
                QiFrame::Discovered { .. } => {
                    panic!("We filtered out all of the Discovered instances already!")
                }
                QiFrame::NewMatch { used: u, .. } => {
                    for used in u.iter() {
                        match used {
                            MatchedTerm::Trigger(t) => {
                                match term_blame.get(&t) {
                                    None => (), //println!("Nobody to blame for {:?}", t),
                                    Some(qi_responsible) =>
                                    // Quantifier instantiation that produced the triggering term
                                    {
                                        if let Some(resp_edges) = graph.get_mut(&qi_responsible) {
                                            resp_edges.insert(*qi_key);
                                        } else {
                                            panic!("Responsible qikey not found!")
                                        }
                                        ()
                                    }
                                }
                            }
                            MatchedTerm::Equality(_t1, _t2) => (), // TODO: Unclear whether/how to use this case
                        }
                    }
                }
            }
        }
        {
            let mut edges: HashMap<(u64, usize), HashSet<(u64, usize)>> = HashMap::new();
            let mut nodes: HashSet<QiKey> = HashSet::new();
            for (src, tgts) in graph.iter() {
                nodes.insert(*src);
                for tgt in tgts {
                    edges
                        .entry((src.key, src.version))
                        .or_insert(std::collections::HashSet::new())
                        .insert((tgt.key, tgt.version));
                    nodes.insert(*tgt);
                }
            }
            let names: HashMap<(u64, usize), String> = nodes
                .iter()
                .map(|k| {
                    let ident = model.instantiations().get(&k).unwrap().frame.quantifier();
                    let name = model.term(ident).expect("not found").name().unwrap();
                    ((k.key, k.version), name.to_owned())
                })
                .collect();
            let nodes = nodes.into_iter().map(|k| (k.key, k.version)).collect();

            InstantiationGraph {
                edges,
                names,
                nodes,
            }
        }
    }
    pub fn total_instantiations(&self) -> u64 {
        self.quantifier_stats
            .iter()
            .fold(0, |acc, cost| acc + cost.instantiations)
    }

    pub fn print_stats(&self) {
        for cost in &self.quantifier_stats {
            let count = cost.instantiations;
            let msg = format!(
                "Instantiated {} {} times ({}% of the total) \n",
                cost.quant,
                count,
                100 * count / self.total_instantiations()
            );
            println!("{}", msg);
        }
    }
}

pub struct BasicApp {
    g: Graph<NodeData, (), Directed>,
}

impl BasicApp {
    fn new(_: &CreationContext<'_>, profiler: Profiler) -> Self {
        let g = generate_graph(&profiler);
        Self { g: Graph::from(&g) }
    }
}

type NodeData = ((u64, usize), String);

fn generate_graph<'a>(profiler: &'a Profiler) -> StableGraph<NodeData, (), Directed> {
    let mut g: StableGraph<NodeData, ()> = StableGraph::new();
    let mut nodes = HashMap::new();
    for node in &profiler.instantiation_graph.nodes {
        let name = profiler.instantiation_graph.names.get(node).unwrap().to_owned();
        let g_node = g.add_node((node.clone(), name));
        nodes.insert(node.clone(), g_node);
    }

    for (src, dsts) in &profiler.instantiation_graph.edges {
        let g_src = nodes.get(src).unwrap();
        for dst in dsts {
            let g_dst = nodes.get(dst).unwrap();
            g.add_edge(g_src.clone(), g_dst.clone(), ());
        }
    }
    g
}

impl App for BasicApp {
    fn update(&mut self, ctx: &Context, _: &mut eframe::Frame) {
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.add(
                &mut GraphView::new(&mut self.g).with_interactions(
                    &SettingsInteraction::default()
                        .with_dragging_enabled(true)
                        .with_selection_enabled(true),
                ).with_custom_node_draw(|ctx, n, state, l| {
                    let node_centre_loc = n.screen_location(state.meta).to_pos2();
                                            let rad = n.screen_radius(state.meta, state.style);

                        // first create rect shape
                        let size = Vec2::new(rad * 1.5, rad * 1.5);
                        let rect = Rect::from_center_size(node_centre_loc, size);
                        let shape_rect = Shape::rect_stroke(
                            rect,
                            Rounding::default(),
                            Stroke::new(1., n.color(ctx)),
                        );

                        // add rect to the layers
                        l.add(shape_rect);

                        // then create label
                        let color = ctx.style().visuals.text_color();
                        let galley = ctx.fonts(|f| {
                            f.layout_no_wrap(
                                n.data().unwrap().1.to_owned(),
                                FontId::new(rad, FontFamily::Monospace),
                                color,
                            )
                        });

                        // we need to offset label by half its size to place it in the center of the rect
                        let offset = Vec2::new(-galley.size().x / 2., -galley.size().y / 2.);

                        // create the shape and add it to the layers
                        let shape_label = TextShape::new(node_centre_loc + offset, galley);
                        l.add(shape_label);

                }),
            );
        });
    }
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let profiler = Profiler::parse(&args.file)?;
    println!("EDGES: ");
    println!("{:?}\n\n", profiler.instantiation_graph.edges);
    println!("NODE NAMES: ");
    println!("{:?}\n\n", profiler.instantiation_graph.names);
    println!("NODES: ");
    println!("{:?}", profiler.instantiation_graph.nodes);
    profiler.print_stats();
    if !args.gui {
        return Ok(());
    }

    let native_options = eframe::NativeOptions::default();
    run_native(
        "SMT quantifier instantiations graph",
        native_options,
        Box::new(|cc| Box::new(BasicApp::new(cc, profiler))),
    )
    .unwrap();
    Ok(())
}
