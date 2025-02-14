use crate::{StepValue, CDF};
use itertools::Itertools;
use std::{cmp::Ordering, collections::BinaryHeap, mem};
use textplots::{Chart, Plot, Shape};

#[derive(Debug, PartialEq, Default, Clone, Copy, serde::Serialize, serde::Deserialize)]
pub enum CompactionMode {
    #[default]
    UnderApproximate,
    OverApproximate,
}

/// Repeated computation with a CDF can lead to an unbounded number of data points, hence we limit its size.
/// This function ensures a maximal data length of `max_size` points by collapsing point pairs that are closest to each other on the x axis.
/// Under CompactionMode::UnderApproximate, the new point gets the greater x coordinate while under CompactionMode::OverApproximate, the new point gets the smaller x coordinate.
/// The resulting point always has the higher y value of the pair.
pub(crate) fn compact(data: &mut Vec<(f32, f32)>, mode: CompactionMode, max_size: usize) {
    {
        let mut pos = 0;
        let mut prev_y = 0.0;
        let mut prev_x = -1.0;
        for i in 0..data.len() {
            let (x, y) = data[i];
            if x == prev_x {
                data[pos - 1] = (x, y);
            } else if y != prev_y {
                data[pos] = (x, y);
                pos += 1;
            }
            prev_x = x;
            prev_y = y;
        }
        data.truncate(pos);
    }

    if data.len() <= max_size {
        return;
    }
    // determine overall scale of the graph to determine the granularity of distances
    // (without this rounding the pruning will be dominated by floating point errors)
    let scale = data[data.len() - 1].0;
    let granularity = scale / 10000.0;

    #[derive(Debug, PartialEq)]
    struct D {
        bin: i16,
        idx: usize,
        dist: f32,
        use_left: bool,
        p: (f32, f32),
    }
    impl Eq for D {}
    impl PartialOrd for D {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for D {
        fn cmp(&self, other: &Self) -> Ordering {
            other
                .bin
                .cmp(&self.bin)
                .then_with(|| self.idx.cmp(&other.idx))
        }
    }
    let mk_d = |dist: f32, idx: usize, use_left: bool, p: (f32, f32)| D {
        bin: (dist / granularity) as i16,
        idx,
        dist,
        use_left,
        p,
    };

    // use a binary heap to pull the closest pairs, identifying them by their x coordinate and sorting them by the distance to their right neighbor.
    //
    // we only consider points whose left and right neighbor are in opposing quadrants (i.e. rising or falling graph around this location)
    let mut heap = data
        .iter()
        .tuple_windows::<(&(f32, f32), &(f32, f32), &(f32, f32))>()
        .enumerate()
        .filter_map(|(idx, (a, b, c))| {
            let use_left = if a.1 >= b.1 && b.1 >= c.1 {
                mode == CompactionMode::OverApproximate
            } else if a.1 <= b.1 && b.1 <= c.1 {
                mode == CompactionMode::UnderApproximate
            } else {
                return None;
            };
            let dist = c.0 - b.0;
            Some(mk_d(dist, idx + 1, use_left, (b.0, b.1)))
        })
        .collect::<BinaryHeap<_>>();

    let mut to_remove = data.len() - max_size;
    while let Some(d) = heap.pop() {
        // skip points that have already been removed
        if data[d.idx].1 < 0.0 {
            continue;
        }
        assert_eq!(d.p, data[d.idx]);

        // just remove this point, meaning that the left neighbour needs to be updated
        let mut neighbours = data[..d.idx]
            .iter()
            .enumerate()
            .rev()
            .filter_map(|(i, (_x, y))| (*y >= 0.0).then_some(i));

        if let Some(neighbour) = neighbours.next() {
            let new_data = if d.use_left {
                data[neighbour]
            } else {
                (data[neighbour].0, data[d.idx].1)
            };

            if let Some(n2) = neighbours.next() {
                // only push to heap if the next neighbour is in the opposite quadrant
                if (data[n2].1 - data[neighbour].1) * (data[neighbour].1 - data[d.idx].1) >= 0.0 {
                    heap.push(mk_d(
                        data[d.idx].0 - data[neighbour].0 + d.dist,
                        d.idx,
                        d.use_left,
                        new_data,
                    ));
                }
            }

            // since we cannot remove the now changed neighbour from the heap, we mark it as removed instead
            // and move the neighbour to our position
            data[d.idx] = new_data;
            data[neighbour].1 = -1.0;

            // let curr_cdf = data
            //     .iter()
            //     .filter(|(_, y)| *y >= 0.0)
            //     .map(|(x, y)| (*x, *y))
            //     .collect::<CDF>();
            // eprintln!("{curr_cdf}");
            // eprintln!("{}", plot_cdf([&orig_cdf, &curr_cdf]));
            // std::io::stdin().read_line(&mut String::new()).unwrap();

            to_remove -= 1;
        }

        if to_remove == 0 {
            break;
        }
    }
    data.retain(|x| x.1 >= 0.0);
}

pub(crate) fn compact_cdf(data: &mut Vec<(f32, CDF)>, mode: CompactionMode, max_size: usize) {
    if data.len() < 10 {
        return;
    }

    let mut pos = 0;
    for idx in 0..data.len() {
        let (x, mut cdf) = mem::take(&mut data[idx]);
        let next_x = data.get(idx + 1).map(|x| x.0).unwrap_or(f32::INFINITY);
        if x.similar(&next_x) {
            continue;
        }
        if cdf.steps().data().len() > max_size {
            let mut steps = cdf.steps().data().to_vec();
            compact(&mut steps, mode, max_size);
            if steps.len() < cdf.steps().data().len() {
                cdf = CDF::new(&steps)
                    .expect("step function error")
                    .with_max_size(max_size)
                    .with_mode(mode);
            }
        }
        if pos == 0 || !cdf.similar(&data[pos - 1].1) {
            data[pos] = (x, cdf);
            pos += 1;
        }
    }
    data.truncate(pos);
}

pub(crate) fn simplify_cdf(data: &mut Vec<(f32, CDF)>) {
    if data.len() < 10 {
        return;
    }
    let max_dx = data[data.len() - 1].0 / 200.0;

    let mut pos = 0;
    let mut current = None;
    for idx in 0..data.len() {
        let (x, cdf) = mem::take(&mut data[idx]);
        let next_x = data.get(idx + 1).map(|x| x.0).unwrap_or(f32::INFINITY);
        if x.similar(&next_x) {
            continue;
        }

        if let Some((curr_x, curr_cdf, count)) = current.take() {
            if next_x - curr_x > max_dx {
                // emit previously summarised CDF
                data[pos] = (curr_x, quantise(curr_cdf));
                pos += 1;
                current = Some((x, cdf, 1.0f32));
            } else {
                // summarise into current CDF
                let merged = curr_cdf
                    .choice(count / (count + 1.0), &cdf)
                    .expect("fractions should be valid");
                current = Some((curr_x, merged, count + 1.0));
            }
        } else {
            current = Some((x, cdf, 1.0f32));
        }
    }
    if let Some((x, cdf, _)) = current.take() {
        data[pos] = (x, quantise(cdf));
        pos += 1;
    }
    data.truncate(pos);
}

fn quantise(cdf: CDF) -> CDF {
    let mut prev = 0.0;
    cdf.iter()
        .map(|(x, y)| (x, (y * 1000.0).round() / 1000.0))
        .filter(|(_, y)| {
            let keep = *y != prev;
            prev = *y;
            keep
        })
        .collect()
}

#[allow(dead_code)]
fn plot_cdf<'a>(cdf: impl IntoIterator<Item = &'a CDF> + 'a) -> String {
    let mut iter = cdf.into_iter().peekable();
    let mut chart = Chart::new(100, 60, 0.0, iter.peek().unwrap().width() * 1.1);
    let shapes = iter
        .map(|cdf| {
            eprintln!("{:?}", cdf.steps().data());
            Shape::Points(&cdf.steps().data())
        })
        .collect::<Vec<_>>();
    let mut chart = &mut chart;
    for shape in &shapes {
        chart = chart.lineplot(shape);
    }
    chart.axis();
    chart.figures();
    format!("{}", chart)
}
