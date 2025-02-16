use super::ShortestPathLink;
use crate::{
    analysis::reverse_topology,
    models::{Latency, Topology},
};
use argmin::{
    core::{observers::ObserverMode, CostFunction, Executor, State},
    solver::particleswarm::ParticleSwarm,
};
use argmin_observer_slog::SlogLogger;
use delta_q::{CompactionMode, DeltaQ, PersistentContext, CDF};
use std::{
    collections::{BTreeMap, HashMap},
    fmt::Write,
};
use terminal_size::{terminal_size, Height, Width};
use textplots::{Chart, Plot, Shape};

pub fn delta_q_analysis(topology: &Topology, report: &mut String, verbose: bool) {
    let reversed_topology = reverse_topology(topology);

    let mut near = CDF::bottom();
    let mut near_count = 0f32;
    let mut far = CDF::bottom();
    let mut far_count = 0f32;

    let mut completion = CDF::bottom();
    let mut completion_count = 0f32;

    let mut hops = BTreeMap::new();
    hops.insert(0, 0);

    let mut latency_at_hop = BTreeMap::<usize, Vec<Latency>>::new();

    for node in reversed_topology.nodes.keys() {
        let sp = crate::analysis::shortest_paths(&reversed_topology, node);

        for (hops, latency) in sp.values().map(|info| (info.hops, info.latency)) {
            latency_at_hop.entry(hops).or_default().push(latency);
        }

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

        get_completion_hops(&sp, &mut hops);
    }

    // disabled using .take(0), but left in as a research tool
    for (hops, mut latencies) in latency_at_hop.into_iter().take(0) {
        latencies.sort();
        let latencies = latencies
            .into_iter()
            .enumerate()
            .map(|(i, latency)| (latency.as_f32(), (i + 1) as f32))
            .collect::<Vec<_>>();
        let plot = plot_steps(&latencies, 200, 100);
        writeln!(report, "{}\nlatency distribution at {} hops", plot, hops).ok();
    }

    let near_compact = near
        .compact(CompactionMode::OverApproximate, 10)
        .choice(0.5, &near.compact(CompactionMode::UnderApproximate, 10))
        .unwrap();

    let far_compact = far
        .compact(CompactionMode::OverApproximate, 10)
        .choice(0.5, &far.compact(CompactionMode::UnderApproximate, 10))
        .unwrap();

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

    writeln!(report, "{}", result).ok();
    add_hops_histogram(report, hops);

    let param = result.state.get_best_param().unwrap().position.as_slice();
    let mut ctx = observation.mk_ctx(param);
    let cdf = ctx.eval("gossip").unwrap().cdf;

    if verbose {
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
    }

    writeln!(report, "\nDeltaQ model:\n\n{}\n", ctx).ok();
    writeln!(report, "{}", plot_cdf([&completion, &cdf])).ok();
    writeln!(report, "Check that the two lines mostly coincide. The smooth line is the topology shortest path diffusion and the more zigzag line is the fitted model.\nUse -v to include model comparison to observation in the ΔQ context.").ok();
}

fn add_hops_histogram(report: &mut String, mut hops: BTreeMap<usize, usize>) {
    if let Some(e) = hops.last_entry() {
        let key = *e.key();
        hops.insert(key + 1, 0);
    }
    let hops = hops
        .into_iter()
        .map(|(hops, count)| (hops as f32, count as f32))
        .collect::<Vec<_>>();
    let mut graph = Chart::new(100, 70, 0.0, 10.0);
    let hop_shape = Shape::Bars(&hops);
    graph.lineplot(&hop_shape);
    graph.axis();
    graph.figures();
    writeln!(report, "{}", graph).ok();
    writeln!(report, "distance distribution in hops ({hops:?})").ok();
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

fn get_completion_hops(
    sp: &HashMap<String, ShortestPathLink>,
    result: &mut BTreeMap<usize, usize>,
) {
    for info in sp.values() {
        *result.entry(info.hops).or_default() += 1;
    }
}

fn line_point_dist(line_start: (f32, f32), line_end: (f32, f32), point: (f32, f32)) -> f32 {
    let a = line_end.0 - line_start.0;
    let b = line_end.1 - line_start.1;
    let c = point.0 - line_start.0;
    let d = point.1 - line_start.1;
    (a * d - b * c).abs() / (a * a + b * b).sqrt()
}

pub fn get_terminal_size() -> (u32, u32) {
    // terminal_size() returns an Option<(Width, Height)>
    if let Some((Width(w), Height(h))) = terminal_size() {
        (w as u32, h as u32)
    } else {
        (120, 90)
    }
}

fn plot_cdf<'a>(cdf: impl IntoIterator<Item = &'a CDF> + 'a) -> String {
    let mut iter = cdf.into_iter().peekable();
    let (w, h) = get_terminal_size();
    let mut chart = Chart::new(w * 2 - 20, h * 3 - 10, 0.0, iter.peek().unwrap().width());
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

fn plot_steps(steps: &[(f32, f32)], width: u32, height: u32) -> String {
    let mut chart = Chart::new(width, height, 0.0, 100.0);
    let shape = Shape::Steps(steps);
    chart.lineplot(&shape);
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
    const NEAR_COMPONENTS: usize = 2;
    const FAR_COMPONENTS: usize = 2;

    pub fn bounds() -> (Vec<f32>, Vec<f32>) {
        (
            vec![0.0; Self::NEAR_COMPONENTS + Self::FAR_COMPONENTS],
            vec![1.0, 10.0, 1.0, 1.0],
        )
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
        const FAR_END: usize = FAR_START + CompletionModel::FAR_COMPONENTS;

        let near_completion = param[0];
        let near_count = param[1] as usize;
        let near_final_weight = 1.0 - (param[1] - (near_count as f32));

        let mut near = mk_choice(
            || DeltaQ::top(),
            near_final_weight,
            || DeltaQ::name(near_name),
        );
        for top_weight in (0..near_count)
            .rev()
            .map(|i| if i != 0 { near_completion } else { 0.0 })
        {
            near = mk_choice(
                || DeltaQ::top(),
                top_weight,
                || DeltaQ::seq(DeltaQ::name(near_name), near),
            );
        }

        let mut far = DeltaQ::name(far_name);
        for &top_weight in param[FAR_START + 1..FAR_END].iter().rev() {
            far = DeltaQ::seq(
                DeltaQ::name(far_name),
                mk_choice(|| DeltaQ::top(), top_weight, || far),
            );
        }
        // in contrast to the near component, the far component permits zero hops
        far = mk_choice(|| DeltaQ::top(), param[FAR_START], || far);

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

fn mk_choice(top: impl FnOnce() -> DeltaQ, weight: f32, bottom: impl FnOnce() -> DeltaQ) -> DeltaQ {
    if weight > 0.9999 {
        top()
    } else if weight < 0.0001 {
        bottom()
    } else {
        DeltaQ::choice(top(), weight, bottom(), 1.0 - weight)
    }
}

impl CostFunction for CompletionModel {
    type Param = Vec<f32>;
    type Output = f32;

    fn cost(&self, param: &Self::Param) -> Result<Self::Output, argmin::core::Error> {
        let result = self.eval(param)?;
        Ok(self.completion.diff2_area(&result))
    }
}
