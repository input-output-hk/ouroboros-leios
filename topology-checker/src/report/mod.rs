use crate::analysis::{
    analyze_network_stats, analyze_stake_distribution, check_triangle_inequality,
};
use crate::analysis::{reverse_topology, ShortestPathLink};
use crate::models::{Latency, Severity, Topology};
use argmin::core::observers::ObserverMode;
use argmin::core::{CostFunction, Executor, State};
use argmin::solver::particleswarm::ParticleSwarm;
use argmin_observer_slog::SlogLogger;
use delta_q::{CompactionMode, DeltaQ, LoadUpdate, PersistentContext, CDF};
use std::collections::HashMap;
use textplots::{Chart, Plot, Shape};

pub fn generate_report(topology: &Topology, filename: &str, start_node: Option<&str>) -> String {
    let mut report = String::new();
    let mut issues = Vec::new();

    // Run analyses
    let network_stats = analyze_network_stats(topology);
    let stake_stats = analyze_stake_distribution(topology);
    issues.extend(check_triangle_inequality(topology));

    // Sort issues by severity and node id
    issues.sort_by_key(|issue| (-(issue.severity as i32), issue.node.clone()));

    // Generate report sections
    report.push_str("# Topology Analysis Report\n\n");
    report.push_str(&format!("Analysis of: {}\n\n", filename));

    // Add network statistics section
    report.push_str("## Network Statistics\n\n");
    report.push_str("| Metric | Value |\n");
    report.push_str("|--------|-------|\n");
    report.push_str(&format!(
        "| Total nodes | {} |\n",
        network_stats.total_nodes
    ));
    report.push_str(&format!(
        "| Block producers | {} |\n",
        network_stats.block_producers
    ));
    report.push_str(&format!(
        "| Relay nodes | {} |\n",
        network_stats.relay_nodes
    ));
    report.push_str(&format!(
        "| Total connections | {} |\n",
        network_stats.total_connections
    ));
    report.push_str(&format!(
        "| Network diameter | {} hops |\n",
        network_stats.network_diameter
    ));
    report.push_str(&format!(
        "| Average connections per node | {:.2} |\n",
        network_stats.avg_connections
    ));
    report.push_str(&format!(
        "| Clustering coefficient | {:.3} |\n",
        network_stats.clustering_coefficient
    ));
    report.push_str(&format!(
        "| Average latency | {:.2} ms |\n",
        network_stats.avg_latency_ms
    ));
    report.push_str(&format!(
        "| Maximum latency | {:.2} ms |\n",
        network_stats.max_latency_ms
    ));
    report.push_str(&format!(
        "| Stake-weighted latency | {:.2} ms |\n",
        network_stats.stake_weighted_latency_ms
    ));
    report.push_str(&format!(
        "| Bidirectional connections | {} |\n",
        network_stats.bidirectional_connections
    ));
    report.push_str(&format!(
        "| Asymmetry ratio | {:.2}% |\n\n",
        network_stats.asymmetry_ratio * 100.0
    ));

    // Add stake distribution section
    report.push_str("## Stake Distribution\n\n");
    report.push_str("| Metric | Value |\n");
    report.push_str("|--------|-------|\n");
    report.push_str(&format!("| Total stake | {} |\n", stake_stats.total_stake));
    report.push_str(&format!(
        "| Gini coefficient | {:.3} |\n\n",
        stake_stats.gini_coefficient
    ));

    report.push_str("### Top 5 Stake Holders\n\n");
    report.push_str("| Node | Stake | % of Total |\n");
    report.push_str("|------|--------|------------|\n");
    for (node, stake) in stake_stats.top_stake_holders {
        let percentage = (stake as f64 / stake_stats.total_stake as f64) * 100.0;
        report.push_str(&format!("| {} | {} | {:.2}% |\n", node, stake, percentage));
    }
    report.push_str("\n");

    report.push_str("### Geographic Stake Distribution\n\n");
    report.push_str("| Region | Nodes | Total Stake | % of Network |\n");
    report.push_str("|---------|--------|-------------|-------------|\n");
    for (region, stats) in stake_stats.geographic_distribution {
        report.push_str(&format!(
            "| {} | {} | {} | {:.2}% |\n",
            region, stats.node_count, stats.total_stake, stats.percentage
        ));
    }
    report.push_str("\n");

    // Add network reliability section
    if !network_stats.critical_nodes.is_empty() {
        report.push_str("## Network Reliability\n\n");
        report.push_str("The following nodes, if removed, would isolate significant stake:\n\n");
        report.push_str("| Node | Isolated Stake | % of Total Stake |\n");
        report.push_str("|------|----------------|------------------|\n");
        for node in &network_stats.critical_nodes {
            report.push_str(&format!(
                "| {} | {} | {:.2}% |\n",
                node.node, node.isolated_stake, node.percentage_of_total
            ));
        }
        report.push_str("\n");
    }

    // Add geographic validation section
    report.push_str("## Geographic Validation\n\n");
    let geo_issues: Vec<_> = issues
        .iter()
        .filter(|i| matches!(i.severity, Severity::Error))
        .collect();

    if geo_issues.is_empty() {
        report.push_str("✅ No geographic violations found\n\n");
    } else {
        report.push_str("### Path Length Violations\n\n");
        for issue in geo_issues {
            report.push_str(&format!("❌ {}\n", issue.message));
            report.push_str(&format!("   Suggestion: {}\n\n", issue.suggestion));
        }
    }

    // Add hop analysis section if a start node is provided
    if let Some(node) = start_node {
        let sp = crate::analysis::shortest_paths(&reverse_topology(topology), node);
        let (near, far) = get_near_far_latencies(&sp);

        eprintln!("{}", near);
        eprintln!("{}", far);
    } else {
        let reversed_topology = reverse_topology(topology);

        let mut near = CDF::bottom();
        let mut near_count = 0f32;
        let mut far = CDF::bottom();
        let mut far_count = 0f32;

        let mut completion = CDF::bottom();
        let mut completion_count = 0f32;

        for node in reversed_topology.nodes.keys() {
            let sp = crate::analysis::shortest_paths(&reversed_topology, node);

            let (near_cdf, far_cdf) = get_near_far_latencies(&sp);
            near = near
                .choice(near_count / (near_count + 1.0), &near_cdf)
                .unwrap();
            near_count += 1.0;
            far = far.choice(far_count / (far_count + 1.0), &far_cdf).unwrap();
            far_count += 1.0;

            let completion_cdf = get_completion_cdf(&sp);
            completion = completion
                .choice(completion_count / (completion_count + 1.0), &completion_cdf)
                .unwrap();
            completion_count += 1.0;
        }

        let near_compact = near
            .compact(CompactionMode::OverApproximate, 10)
            .choice(0.5, &near.compact(CompactionMode::UnderApproximate, 10))
            .unwrap();

        let far_compact = far
            .compact(CompactionMode::OverApproximate, 10)
            .choice(0.5, &far.compact(CompactionMode::UnderApproximate, 10))
            .unwrap();

        eprintln!("{completion_count}");

        let observation = CompletionModel {
            near: DeltaQ::cdf(near_compact),
            far: DeltaQ::cdf(far_compact),
            completion: completion.clone(),
        };

        let solver = ParticleSwarm::<Vec<f32>, f32, _>::new(CompletionModel::bounds(), 40);
        let result = Executor::new(observation.clone(), solver)
            .configure(|state| state.max_iters(100))
            .add_observer(SlogLogger::term(), ObserverMode::Always)
            .run()
            .unwrap();

        eprintln!("{}", result);

        let param = result.state.get_best_param().unwrap().position.as_slice();
        let mut ctx = observation.mk_ctx(param);
        let cdf = ctx.eval("gossip").unwrap().cdf;

        ctx.put_comment("\n\n-- this is the completion model that was fitted to the topology\n");
        ctx.put(
            "short_path_completion".into(),
            CompletionModel::expr(param, "near_send", "far_send"),
        );

        ctx.put_comment("\n\n-- these are the completion CDFs from the topology in full detail\n");
        ctx.put("observation".into(), DeltaQ::cdf(completion.clone()));
        ctx.put("obs_near".into(), DeltaQ::cdf(near));
        ctx.put("obs_far".into(), DeltaQ::cdf(far));

        ctx.set_constraint("short_path_completion", Some("observation".into()));
        ctx.set_constraint("near_send", Some("obs_near".into()));
        ctx.set_constraint("far_send", Some("obs_far".into()));

        eprintln!("{}", ctx);
        eprintln!("{}", plot_cdf([&completion, &cdf]));
    }

    report
}

fn get_near_far_latencies(sp: &HashMap<String, ShortestPathLink>) -> (CDF, CDF) {
    let mut latencies = sp.values().map(|info| info.latency).collect::<Vec<_>>();
    latencies.sort();
    let latencies = latencies
        .iter()
        .enumerate()
        .map(|(i, latency)| (i as f32, latency.as_f32()))
        .collect::<Vec<_>>();

    let line_start = latencies[0];
    let line_end = latencies[latencies.len() - 1];
    let max_dist = latencies
        .iter()
        .map(|&(x, y)| line_point_dist(line_start, line_end, (x, y)))
        .max_by(|a, b| a.total_cmp(b))
        .unwrap()
        / 1.1;
    let first_cut = latencies
        .iter()
        .position(|&(x, y)| line_point_dist(line_start, line_end, (x, y)) > max_dist)
        .unwrap();
    let second_cut = latencies
        .iter()
        .rposition(|&(x, y)| line_point_dist(line_start, line_end, (x, y)) > max_dist)
        .unwrap();

    // here x is node count and y is latency, so we need to turn them around
    let near = latencies[0..first_cut]
        .iter()
        .map(|&(x, y)| (y, (x + 1.0) / (first_cut as f32)))
        .collect();
    let far = latencies[second_cut + 1..]
        .iter()
        .map(|&(x, y)| {
            (
                y,
                (x - second_cut as f32) / (latencies.len() - second_cut - 1) as f32,
            )
        })
        .collect();

    (near, far)
}

fn get_completion_cdf(sp: &HashMap<String, ShortestPathLink>) -> CDF {
    let mut latencies = sp.values().map(|info| info.total).collect::<Vec<_>>();
    latencies.sort();
    let mut prev_latency = Latency::zero();
    let scale = 1.0 / (latencies.len() as f32);
    let latencies = latencies
        .into_iter()
        .enumerate()
        .rev()
        .filter_map(|(i, latency)| {
            (latency != prev_latency).then(|| {
                prev_latency = latency;
                (latency.as_f32(), (i + 1) as f32 * scale)
            })
        })
        .collect::<Vec<_>>();
    latencies.into_iter().rev().collect()
}

fn line_point_dist(line_start: (f32, f32), line_end: (f32, f32), point: (f32, f32)) -> f32 {
    let a = line_end.0 - line_start.0;
    let b = line_end.1 - line_start.1;
    let c = point.0 - line_start.0;
    let d = point.1 - line_start.1;
    (a * d - b * c).abs() / (a * a + b * b).sqrt()
}

#[allow(dead_code)]
fn plot_cdf<'a>(cdf: impl IntoIterator<Item = &'a CDF> + 'a) -> String {
    let mut iter = cdf.into_iter().peekable();
    let mut chart = Chart::new(400, 300, 0.0, iter.peek().unwrap().width());
    let shapes = iter
        .map(|cdf| Shape::Steps(&cdf.steps().data()))
        .collect::<Vec<_>>();
    for shape in &shapes {
        chart.lineplot(shape);
    }
    chart.axis();
    chart.figures();
    format!("{}", chart)
}

#[derive(Debug, Clone)]
pub struct CompletionModel {
    pub near: DeltaQ,
    pub far: DeltaQ,
    pub completion: CDF,
}

impl CompletionModel {
    const NEAR_COMPONENTS: usize = 3;
    const FAR_COMPONENTS: usize = 3;

    pub fn bounds() -> (Vec<f32>, Vec<f32>) {
        (vec![0.0; 6], vec![1.0; 6])
    }

    /// Create the DeltaQ model from a list of parameters.
    ///
    /// The general idea is that the gossip consists of near and far components, each governed by
    /// their respective link latency CDFs. The first three parameters control the near component,
    /// the last three control the far component, where each parameter is the probability of
    /// having completed the gossip at the respective hop. Note that the near component unconditionally
    /// performs one hop while the far component may be absent completely.
    pub fn expr(param: &[f32], near_name: &str, far_name: &str) -> DeltaQ {
        const FAR_START: usize = CompletionModel::NEAR_COMPONENTS;
        const FAR_LAST: usize = FAR_START + CompletionModel::FAR_COMPONENTS - 1;

        let mut near = DeltaQ::name(near_name);
        for &top_weight in param[0..FAR_START].iter().rev() {
            if top_weight > 0.9999 {
                // unconditional completion, so simplify away the choice operator;
                // sequence with TOP is a no-op
                near = DeltaQ::name(near_name);
            } else if top_weight < 0.0001 {
                // completion not possible, so sequence with unconditional hop
                near = DeltaQ::seq(DeltaQ::name(near_name), near);
            } else {
                // otherwise, sequence with hop and choice of completion
                near = DeltaQ::seq(
                    DeltaQ::name(near_name),
                    DeltaQ::choice(DeltaQ::top(), top_weight, near, 1.0 - top_weight),
                );
            }
        }

        let mut far = DeltaQ::name(far_name);
        for &top_weight in param[FAR_START..FAR_LAST].iter().rev() {
            if top_weight > 0.9999 {
                far = DeltaQ::name(far_name);
            } else if top_weight < 0.0001 {
                far = DeltaQ::seq(DeltaQ::name(far_name), far);
            } else {
                far = DeltaQ::seq(
                    DeltaQ::name(far_name),
                    DeltaQ::choice(DeltaQ::top(), top_weight, far, 1.0 - top_weight),
                );
            }
        }
        // in contrast to the near component, the far component permits zero hops
        far = DeltaQ::choice(DeltaQ::top(), param[FAR_LAST], far, 1.0 - param[FAR_LAST]);

        DeltaQ::seq(near, far)
    }

    pub fn mk_ctx(&self, param: &[f32]) -> PersistentContext {
        let mut ctx = PersistentContext::default();
        ctx.put_comment("-- this is the main result expression\n");
        ctx.put("gossip".into(), Self::expr(param, "near", "far"));
        ctx.put_comment(
            "\n\n-- gossip is built on these outcomes that should contain send and receive actions\n",
        );
        ctx.put("near".into(), DeltaQ::name("near_send"));
        ctx.put("far".into(), DeltaQ::name("far_send"));
        ctx.put_comment("\n\n-- these are the extracted latencies from the topology\n");
        ctx.put("near_send".into(), self.near.clone());
        ctx.put("far_send".into(), self.far.clone());
        ctx
    }

    pub fn eval(&self, param: &[f32]) -> Result<CDF, argmin::core::Error> {
        let ctx = self.mk_ctx(param);
        Ok(ctx
            .eval("gossip")
            .map_err(|e| argmin::core::Error::new(e))?
            .cdf)
    }
}

impl CostFunction for CompletionModel {
    type Param = Vec<f32>;
    type Output = f32;

    fn cost(&self, param: &Self::Param) -> Result<Self::Output, argmin::core::Error> {
        let result = self.eval(param)?;
        Ok(self.completion.diff_area(&result))
    }
}
