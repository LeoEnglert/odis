//! Upper-neighbor computation for concept lattices.

use bit_set::BitSet;

use crate::FormalContext;

/// Returns the canonical generator set for all upper neighbors of the concept with extent `input`.
///
/// For each object `m ∉ input`, `m` is a generator if `hull(input ∪ {m})` does not subsume any
/// other candidate generator still in the working set. The result is the set of such minimal
/// generators — one per distinct upper neighbor — following Lindig's upper-neighbor algorithm.
pub fn index_upper_neighbor<T>(input: &BitSet, context: &FormalContext<T>) -> BitSet {
    // Objects not in the current extent
    let diff_set: BitSet = (0..context.objects.len())
        .collect::<BitSet>()
        .difference(input)
        .collect();

    let mut output = diff_set.clone();

    for m in &diff_set {
        let mut set_m = BitSet::new();
        set_m.insert(m);

        // Calculate closure of (input U {m})
        let hull_input_m = context.index_object_hull(&input.union(&set_m).collect());

        let hull_input_m_and_output = hull_input_m.intersection(&output).collect::<BitSet>();

        // If the closure subsumes other candidates, m is not a minimal generator.
        if hull_input_m_and_output != set_m {
            output.difference_with(&set_m);
        }
    }
    output
}
