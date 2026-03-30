//! Branch-and-bound DimDraw lattice drawing algorithm.

use std::collections::HashMap;
#[cfg(not(target_arch = "wasm32"))]
use std::time::{Duration, Instant};
#[cfg(target_arch = "wasm32")]
fn now_ms() -> f64 {
    web_sys::window()
        .and_then(|w| w.performance())
        .map(|p| p.now())
        .unwrap_or(0.0)
}

use bit_set::BitSet;
use crate::data_structures::{drawing::Drawing, lattice::Lattice, poset::Poset};
use crate::traits::DrawingAlgorithm;

// Each row of the transitive closure is a BitSet of strict successors:
// tc[u] = { v : u < v in the (partial) order }.
type Tc = Vec<BitSet>;

// Memoization state key: canonical sorted representation of two Tc matrices.
type StateKey = (Vec<Vec<usize>>, Vec<Vec<usize>>);

/// Fast branch-and-bound lattice drawing algorithm.
///
/// The search is time-bounded by `timeout_ms`.
///
/// - `timeout_ms > 0`: stop exploring new branches when the budget is reached.
/// - `timeout_ms == 0`: unbounded search.
///
/// Timeout does not count as failure: the best valid solution found so far is returned.
pub struct DimDraw {
    /// Search budget in milliseconds. `0` means unbounded search.
    pub timeout_ms: u64,
}

struct SolverRuntime {
    best_cost: u32,
    best_tc1: Tc,
    best_tc2: Tc,
    memo: HashMap<StateKey, u32>,
    nodes_explored: usize,
    #[cfg(not(target_arch = "wasm32"))]
    start_time: Instant,
    #[cfg(target_arch = "wasm32")]
    start_ms: f64,
    timeout_ms: u64,
    timed_out: bool,
}

impl SolverRuntime {
    fn new(best_cost: u32, best_tc1: Tc, best_tc2: Tc, timeout_ms: u64) -> Self {
        Self {
            best_cost,
            best_tc1,
            best_tc2,
            memo: HashMap::new(),
            nodes_explored: 0,
            #[cfg(not(target_arch = "wasm32"))]
            start_time: Instant::now(),
            #[cfg(target_arch = "wasm32")]
            start_ms: now_ms(),
            timeout_ms,
            timed_out: false,
        }
    }

    #[inline(always)]
    fn has_timed_out(&self) -> bool {
        #[cfg(not(target_arch = "wasm32"))]
        {
            self.timeout_ms > 0
                && self.start_time.elapsed() >= Duration::from_millis(self.timeout_ms)
        }
        #[cfg(target_arch = "wasm32")]
        {
            self.timeout_ms > 0
                && (now_ms() - self.start_ms) >= self.timeout_ms as f64
        }
    }
}

#[allow(dead_code)] // fields only read in #[cfg(test)] code
pub(crate) struct SearchOutcome {
    pub(crate) drawing: Drawing,
    pub(crate) best_cost: usize,
    pub(crate) baseline_cost: usize,
    pub(crate) explored_nodes: usize,
    pub(crate) timed_out: bool,
}

/// Adds `u < v` to transitive closure `tc` (mutating a copy), returns None on cycle.
#[inline]
fn add_edge_logic(tc: &Tc, u: usize, v: usize) -> Option<Tc> {
    if tc[u].contains(v) {
        return Some(tc.clone()); // already ordered
    }
    if tc[v].contains(u) {
        return None; // cycle
    }
    let mut new_tc = tc.clone();
    let mut mask = new_tc[v].clone();
    mask.insert(v);
    for row in &mut new_tc {
        if row.contains(u) {
            row.union_with(&mask);
        }
    }
    new_tc[u].union_with(&mask);
    Some(new_tc)
}

/// Build initial transitive closure from covering edges.
fn initialize_transitive_closure(node_count: usize, edges: &[(usize, usize)]) -> Option<Tc> {
    let mut tc = vec![BitSet::new(); node_count];
    for &(u, v) in edges {
        tc = add_edge_logic(&tc, u, v)?;
    }
    Some(tc)
}

/// Precompute `not_orig[i]` = set of all nodes NOT reachable from i in the original order.
#[inline]
fn precompute_not_orig(tc_orig: &Tc, node_count: usize) -> Tc {
    let all: BitSet = (0..node_count).collect();
    tc_orig.iter().map(|row| all.difference(row).collect::<BitSet>()).collect()
}

/// Extract incomparable pairs, sorted by descending degree-product (most-constrained first).
fn extract_incomparable_pairs(tc_orig: &Tc) -> Vec<(usize, usize)> {
    let n = tc_orig.len();
    let mut degrees = vec![0u32; n];
    let mut raw_pairs = Vec::new();

    for u in 0..n {
        for v in (u + 1)..n {
            if !tc_orig[u].contains(v) && !tc_orig[v].contains(u) {
                raw_pairs.push((u, v));
                degrees[u] += 1;
                degrees[v] += 1;
            }
        }
    }

    raw_pairs.sort_by_key(|&(u, v)| std::cmp::Reverse(degrees[u] as u64 * degrees[v] as u64));
    raw_pairs
}

/// Compute global forced-agreement cost (fewer is better).
#[inline]
fn global_cost(tc1: &Tc, tc2: &Tc, not_orig: &Tc) -> u32 {
    tc1.iter()
        .zip(tc2.iter())
        .zip(not_orig.iter())
        .map(|((a, b), no)| a.iter().filter(|&x| b.contains(x) && no.contains(x)).count() as u32)
        .sum()
}

/// Build a strong initial candidate using the basis-map heuristic.
fn heuristic_initial_candidate(tc_orig: &Tc, not_orig: &Tc) -> (Tc, Tc, u32) {
    let n = tc_orig.len();

    // basis = nodes with <= 1 immediate upper cover in tc_orig
    let mut basis = Vec::new();
    for x in 0..n {
        let mut covers = 0u32;
        'outer: for y in tc_orig[x].iter() {
            let mut is_cover = true;
            for z in tc_orig[x].iter() {
                if z != y && tc_orig[z].contains(y) {
                    is_cover = false;
                    break;
                }
            }
            if is_cover {
                covers += 1;
                if covers > 1 {
                    break 'outer;
                }
            }
        }
        if covers <= 1 {
            basis.push(x);
        }
    }

    if basis.is_empty() {
        basis.extend(0..n);
    }
    basis.sort_by_key(|&x| tc_orig[x].len());

    let mut top_sort: Vec<usize> = (0..n).collect();
    top_sort.sort_by_key(|&x| tc_orig[x].len());
    let mut top_sort_idx = vec![0usize; n];
    for (idx, &node) in top_sort.iter().enumerate() {
        top_sort_idx[node] = idx;
    }

    // m[x] = set of basis indices k where basis[k] >= x (i.e. x == basis[k] or x < basis[k])
    let build_tc_from_basis_order = |pi: &[usize]| -> Tc {
        let mut m: Vec<BitSet> = vec![BitSet::new(); n];
        for (k, &jk) in pi.iter().enumerate() {
            for x in 0..n {
                if x == jk || tc_orig[x].contains(jk) {
                    m[x].insert(k);
                }
            }
        }
        let mut l_seq: Vec<usize> = (0..n).collect();
        // Nodes with fewer basis elements above them are higher in the lattice and
        // must come first so that tc_full[node] encodes their strict successors.
        l_seq.sort_by_key(|&x| (m[x].len(), top_sort_idx[x]));
        let mut tc_full: Tc = vec![BitSet::new(); n];
        let mut current: BitSet = BitSet::new();
        for node in l_seq {
            tc_full[node] = current.clone();
            current.insert(node);
        }
        tc_full
    };

    let pi_1 = basis.clone();
    let mut pi_2 = basis;
    pi_2.reverse();

    let tc1 = build_tc_from_basis_order(&pi_1);
    let tc2 = build_tc_from_basis_order(&pi_2);
    let cost = global_cost(&tc1, &tc2, not_orig);
    (tc1, tc2, cost)
}

fn positions_from_tc(tc: &Tc) -> Vec<f64> {
    let n = tc.len();
    tc.iter()
        .map(|row| (n.saturating_sub(1 + row.len())) as f64)
        .collect()
}

fn project_linear_extensions_to_drawing(tc1: &Tc, tc2: &Tc) -> Drawing {
    let n = tc1.len();
    let p1 = positions_from_tc(tc1);
    let p2 = positions_from_tc(tc2);

    let coordinates: Vec<(f64, f64)> = (0..n).map(|i| (p1[i] - p2[i], -(p1[i] + p2[i]))).collect();
    Drawing::new(coordinates)
}

fn tc_to_key(tc: &Tc) -> Vec<Vec<usize>> {
    tc.iter().map(|bs| bs.iter().collect()).collect()
}

#[inline]
fn canonical_state_key(tc1: &Tc, tc2: &Tc) -> StateKey {
    let k1 = tc_to_key(tc1);
    let k2 = tc_to_key(tc2);
    if k1 <= k2 { (k1, k2) } else { (k2, k1) }
}

fn search(
    runtime: &mut SolverRuntime,
    tc1: Tc,
    tc2: Tc,
    pair_idx: usize,
    pairs: &[(usize, usize)],
    not_orig: &Tc,
) {
    runtime.nodes_explored += 1;

    if runtime.has_timed_out() {
        runtime.timed_out = true;
        return;
    }

    let cost = global_cost(&tc1, &tc2, not_orig);
    if cost >= runtime.best_cost {
        return;
    }

    let key = canonical_state_key(&tc1, &tc2);
    if let Some(&prev) = runtime.memo.get(&key) {
        if prev <= cost {
            return;
        }
    }
    runtime.memo.insert(key, cost);

    // Skip pairs already resolved in both extensions.
    let mut idx = pair_idx;
    while idx < pairs.len() {
        let (u, v) = pairs[idx];
        if (tc1[u].contains(v) || tc1[v].contains(u)) && (tc2[u].contains(v) || tc2[v].contains(u)) {
            idx += 1;
        } else {
            break;
        }
    }

    if idx == pairs.len() {
        runtime.best_cost = cost;
        runtime.best_tc1 = tc1;
        runtime.best_tc2 = tc2;
        return;
    }

    let (u, v) = pairs[idx];
    // Branching order matches Python: incomparable-first (u<v in L1, v<u in L2),
    // then both-same (forced agreements). This ordering matters for pruning quality.
    let choices: [(usize, usize, usize, usize); 4] = [
        (u, v, v, u),
        (v, u, u, v),
        (u, v, u, v),
        (v, u, v, u),
    ];

    for (u1, v1, u2, v2) in choices {
        if runtime.has_timed_out() {
            runtime.timed_out = true;
            return;
        }

        let Some(next_tc1) = add_edge_logic(&tc1, u1, v1) else {
            continue;
        };
        let Some(next_tc2) = add_edge_logic(&tc2, u2, v2) else {
            continue;
        };

        search(runtime, next_tc1, next_tc2, idx + 1, pairs, not_orig);
    }
}

impl DimDraw {
    /// Core solver operating directly on a `Poset`. Avoids the `Lattice` wrapper
    /// so that iceberg posets (which may lack a unique top/bottom) can be drawn.
    pub(crate) fn solve_from_poset<T>(&self, poset: &Poset<T>) -> Option<SearchOutcome> {
        let node_count = poset.nodes.len();
        if node_count == 0 {
            return None;
        }
        if node_count == 1 {
            return Some(SearchOutcome {
                drawing: Drawing::new(vec![(0.0, 0.0)]),
                best_cost: 0,
                baseline_cost: 0,
                explored_nodes: 1,
                timed_out: false,
            });
        }

        let edges: Vec<(usize, usize)> = poset
            .covering_edges
            .iter()
            .map(|&(u, v)| (u as usize, v as usize))
            .collect();

        let tc_orig = initialize_transitive_closure(node_count, &edges)?;
        let not_orig = precompute_not_orig(&tc_orig, node_count);
        let pairs = extract_incomparable_pairs(&tc_orig);

        let (base_tc1, base_tc2, baseline_cost) = heuristic_initial_candidate(&tc_orig, &not_orig);

        let mut runtime = SolverRuntime::new(baseline_cost, base_tc1, base_tc2, self.timeout_ms);
        search(
            &mut runtime,
            tc_orig.clone(),
            tc_orig,
            0,
            &pairs,
            &not_orig,
        );

        let drawing = project_linear_extensions_to_drawing(&runtime.best_tc1, &runtime.best_tc2);
        if drawing.coordinates.len() != node_count {
            return None;
        }
        if !drawing
            .coordinates
            .iter()
            .all(|(x, y)| x.is_finite() && y.is_finite())
        {
            return None;
        }

        Some(SearchOutcome {
            drawing,
            best_cost: runtime.best_cost as usize,
            baseline_cost: baseline_cost as usize,
            explored_nodes: runtime.nodes_explored,
            timed_out: runtime.timed_out,
        })
    }

    pub(crate) fn solve_with_stats<T>(&self, lattice: &Lattice<T>) -> Option<SearchOutcome> {
        self.solve_from_poset(&lattice.poset)
    }
}

impl DrawingAlgorithm for DimDraw {
    fn draw<T>(&self, lattice: &Lattice<T>) -> Option<Drawing> {
        self.solve_with_stats(lattice).map(|outcome| outcome.drawing)
    }

    fn draw_poset<T: Clone>(&self, poset: &Poset<T>) -> Option<Drawing> {
        self.solve_from_poset(poset).map(|outcome| outcome.drawing)
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::time::{Duration, Instant};

    use super::DimDraw;
    use crate::traits::DrawingAlgorithm;
    use crate::FormalContext;

    fn living_beings_lattice() -> crate::data_structures::lattice::Lattice<(bit_set::BitSet, bit_set::BitSet)> {
        let ctx = FormalContext::<String>::from(&fs::read("test_data/living_beings_and_water.cxt").unwrap())
            .unwrap();
        ctx.concept_lattice().expect("concept_lattice returned None")
    }

    #[test]
    fn test_dimdraw_timeout_returns_coordinate_per_node() {
        let lattice = living_beings_lattice();
        let out = DimDraw { timeout_ms: 1 }
            .solve_with_stats(&lattice)
            .expect("DimDraw should return an outcome");

        assert_eq!(out.drawing.coordinates.len(), lattice.poset.nodes.len());
        assert!(
            out.drawing
                .coordinates
                .iter()
                .all(|(x, y)| x.is_finite() && y.is_finite())
        );
    }

    #[test]
    fn test_dimdraw_result_cost_not_worse_than_initial_baseline() {
        let lattice = living_beings_lattice();
        let out = DimDraw { timeout_ms: 1 }
            .solve_with_stats(&lattice)
            .expect("DimDraw should return an outcome");

        assert!(
            out.best_cost <= out.baseline_cost,
            "best cost {} should be <= baseline {}",
            out.best_cost,
            out.baseline_cost
        );
    }

    #[test]
    fn test_dimdraw_larger_budget_explores_at_least_as_much() {
        let lattice = living_beings_lattice();

        let short = DimDraw { timeout_ms: 1 }
            .solve_with_stats(&lattice)
            .expect("short run should produce outcome");
        let long = DimDraw { timeout_ms: 50 }
            .solve_with_stats(&lattice)
            .expect("long run should produce outcome");

        assert!(
            long.explored_nodes >= short.explored_nodes,
            "expected longer budget to explore at least as much (short={}, long={})",
            short.explored_nodes,
            long.explored_nodes
        );
    }

    #[test]
    fn test_dimdraw_draw_returns_some_on_valid_lattice() {
        let lattice = living_beings_lattice();
        let drawing = DimDraw { timeout_ms: 10 }.draw(&lattice);
        assert!(drawing.is_some());
    }

    #[test]
    #[ignore = "profiling helper; run manually with --ignored --nocapture"]
    fn profile_dimdraw_fm3_unbounded() {
        let ctx = FormalContext::<String>::from(&fs::read("test_data/fm3.cxt").unwrap()).unwrap();
        let lattice = ctx.concept_lattice().expect("concept_lattice returned None");

        let started = Instant::now();
        let out = DimDraw { timeout_ms: 0 }
            .solve_with_stats(&lattice)
            .expect("DimDraw should return an outcome");
        let elapsed = started.elapsed();

        eprintln!(
            "fm3: elapsed={:?}, nodes={}, baseline_cost={}, best_cost={}",
            elapsed, out.explored_nodes, out.baseline_cost, out.best_cost
        );

        // Keep this generous enough for debug CI while still catching pathological regressions.
        assert!(
            elapsed <= Duration::from_secs(3),
            "unexpectedly slow fm3 solve: {:?}",
            elapsed
        );
    }
}
