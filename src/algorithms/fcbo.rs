//! Fast Close-by-One (FCBO) concept enumeration algorithm.

use bit_set::BitSet;
use std::collections::HashMap;

use crate::FormalContext;

// Based on the algorithm presented in: https://www.sciencedirect.com/science/article/abs/pii/S0020025511004804?via%3Dihub

/// Enum containing the different outcomes of calling `fcbo_next_concept`
enum OutputType {
    /// Contains a newly computed formal concept and its index position
    FormalConcept(
        /// Tuple containing one formal concept (Extent, Intent)
        (BitSet, BitSet),
        /// The index of the inner for loop
        usize,
    ),
    /// Contains a new dead end attribute set and its index position
    DeadEndAttributes(
        /// One new dead end attribute set
        BitSet,
        /// The index of the inner for loop
        usize,
    ),
    /// Signals that a full node was cleared
    NodeCleared,
}

/// Struct used as queue entries containing the calling context for `fcbo_next_concept`
struct CallingContext {
    /// Set of input attributes
    input_attr: BitSet,
    /// Index of the inner for loop
    inner_index: usize,
    /// Sets of dead end attributes
    dead_end_attr: Option<HashMap<usize, BitSet>>,
}

impl CallingContext {
    /// Creates a new instance of itself, the dead end attribute sets are added after the next node is cleared
    fn new(input_attr: BitSet, inner_index: usize) -> Self {
        CallingContext {
            input_attr,
            inner_index,
            dead_end_attr: None,
        }
    }
}

/// New canonicity test added in paper to prevent duplicate branches
fn canonicity_test_one(
    smaller_subsets: &[BitSet],
    inner_index: usize,
    input_attributes: &BitSet,
    dead_end_attr_set: &HashMap<usize, BitSet>,
) -> bool {
    let intersection_dead = dead_end_attr_set
        .get(&inner_index)
        .unwrap()
        .intersection(&smaller_subsets[inner_index])
        .collect::<BitSet>();

    let intersection_input = input_attributes
        .intersection(&smaller_subsets[inner_index])
        .collect();

    intersection_dead.is_subset(&intersection_input)
}

/// Old canonicity test from paper
fn canonicity_test_two(
    smaller_subsets: &[BitSet],
    inner_index: usize,
    input_attributes: &BitSet,
    next_attributes: &BitSet,
) -> bool {
    let intersection_input: BitSet = input_attributes
        .intersection(&smaller_subsets[inner_index])
        .collect();

    let intersection_next: BitSet = next_attributes
        .intersection(&smaller_subsets[inner_index])
        .collect();

    intersection_input == intersection_next
}

/// Calculates a single OutputType enum.
/// Closely follows the pseudo code from paper but leaves out the halting condition which is checked in `fcbo_concepts`.
fn fcbo_next_concept<T>(
    context: &FormalContext<T>,
    smaller_subsets: &[BitSet],
    input_attributes: &BitSet,
    inner_index: usize,
    dead_end_attr_set: &HashMap<usize, BitSet>,
) -> OutputType {
    for j in inner_index..context.attributes.len() {
        if !input_attributes.contains(j)
            && canonicity_test_one(smaller_subsets, j, input_attributes, dead_end_attr_set)
        {
            let mut new_attr = BitSet::new();
            new_attr.insert(j);

            let next_objects: BitSet = context
                .index_extent(input_attributes)
                .intersection(&context.index_extent(&new_attr))
                .collect();
            let next_attributes = context.index_intent(&next_objects);

            if canonicity_test_two(smaller_subsets, j, input_attributes, &next_attributes) {
                return OutputType::FormalConcept((next_objects, next_attributes), j);
            } else {
                return OutputType::DeadEndAttributes(next_attributes, j);
            }
        }
    }
    OutputType::NodeCleared
}

/// Returns an iterator which produces formal concepts.
/// The concepts are only calculated when requested with `.next()` or `.collect()`.
/// Implements the FCBO algorithm.
pub fn index_fcbo_concepts<'a, T>(
    context: &'a FormalContext<T>,
) -> impl Iterator<Item = (BitSet, BitSet)> + 'a {
    // Constant used throughout the function
    let attr_length = context.attributes.len();

    // Subsets needed by the canonicity tests from the paper
    // smaller_subsets[i] contains {0, ..., i-1}
    let mut smaller_subsets: Vec<BitSet> = Vec::with_capacity(attr_length);
    for i in 0..attr_length {
        smaller_subsets.push((0..i).collect());
    }

    // The first formal concept, usually ({"all objects"}, {}) or the closure of empty set
    let starting_objects = context.index_extent(&BitSet::new());
    let mut input_attributes = context.index_intent(&starting_objects);

    // Set the starting attribute of the for loop of fcbo_next_concepts to 0
    let mut inner_index = 0;

    // The first dead end attribute set initialized with empty sets to pass the first canonicity test
    let mut dead_end_attr_set = HashMap::new();
    for i in 0..attr_length {
        dead_end_attr_set.insert(i, BitSet::new());
    }

    // Queue containing calling context of fcbo_next_concept
    let mut queue: Vec<CallingContext> = Vec::new();

    // Records the number of branches that a node generates
    let mut branches: usize = 0;

    // Condition to print the first formal concept
    let mut first_concept = true;

    std::iter::from_fn(move || {
        // Returns the first concept and is then skipped
        if first_concept {
            first_concept = false;
            return Some((starting_objects.clone(), input_attributes.clone()));
        }

        // Loops until a new formal concept is returned by fcbo_next_concept
        loop {
            let output = fcbo_next_concept(
                context,
                &smaller_subsets,
                &input_attributes,
                inner_index,
                &dead_end_attr_set,
            );

            match output {
                // 1: New concept is added to queue and the concept is returned.
                OutputType::FormalConcept(formal_concept, previous_inner_index) => {
                    // Increments the index for the next call of fcbo_next_concept
                    inner_index = previous_inner_index + 1;

                    // Checks the halting condition before adding the new concept to queue to prevent unnecessary queue entries
                    // (If the concept intent is full set and index reached end?)
                    if formal_concept.1 != (0..attr_length).collect()
                        && previous_inner_index < attr_length - 1
                    {
                        branches += 1;
                        queue.push(CallingContext::new(formal_concept.1.clone(), inner_index));
                    }
                    return Some(formal_concept);
                }
                // 2: Saves the new dead end attribute and increments the index.
                OutputType::DeadEndAttributes(dead_end_attributes, previous_inner_index) => {
                    dead_end_attr_set.insert(previous_inner_index, dead_end_attributes);
                    inner_index = previous_inner_index + 1;
                }
                // 3: Finishes algorithm upon empty queue or updates calling context.
                OutputType::NodeCleared => {
                    if queue.is_empty() {
                        return None;
                    }
                    // If branches were generated, the next dead end attributes are added to their queue entries
                    if branches != 0 {
                        // Clean up dead end sets that are no longer needed
                        for j in 0..queue[queue.len() - branches].inner_index {
                            dead_end_attr_set.remove(&j);
                        }
                        // Copy current dead end sets to all branches generated at this level?
                        // The logic seems to distribute the learned dead ends to siblings.
                        for i in (queue.len() - branches)..(queue.len()) {
                            queue[i].dead_end_attr = Some(dead_end_attr_set.clone());
                        }
                        branches = 0;
                    }
                    // Processes the back queue entry (LIFO - DFS)
                    let state = queue.pop().unwrap();
                    input_attributes = state.input_attr;
                    inner_index = state.inner_index;
                    dead_end_attr_set = state.dead_end_attr.unwrap();
                }
            }
        }
    })
}

/// Zero-size handle for the FCbO concept enumeration algorithm.
pub struct Fcbo;

impl<T> crate::traits::ConceptEnumerator<T> for Fcbo {
    fn enumerate_concepts<'ctx>(
        &self,
        context: &'ctx crate::FormalContext<T>,
    ) -> impl Iterator<Item = (BitSet, BitSet)> + 'ctx {
        index_fcbo_concepts(context)
    }
}

#[cfg(test)]
mod tests {
    use crate::{algorithms::fcbo::index_fcbo_concepts, FormalContext};
    use bit_set::BitSet;
    use itertools::Itertools;
    use std::{collections::BTreeSet, fs};

    #[test]
    fn test_data_1() {
        let context = FormalContext::<String>::from(
            &fs::read("test_data/living_beings_and_water.cxt").unwrap(),
        )
        .unwrap();

        let concepts: BTreeSet<_> = index_fcbo_concepts(&context).map(|(_, x)| x).collect();

        let mut concepts_val = BTreeSet::new();
        for ms in (0..context.attributes.len()).powerset() {
            let sub: BitSet = ms.into_iter().collect();
            let hull = context.index_attribute_hull(&sub);
            if sub == hull {
                concepts_val.insert(hull);
            }
        }
        assert_eq!(concepts, concepts_val);
    }

    #[test]
    fn test_data_2() {
        let context =
            FormalContext::<String>::from(&fs::read("test_data/eu.cxt").unwrap()).unwrap();

        let concepts: BTreeSet<_> = index_fcbo_concepts(&context).map(|(_, x)| x).collect();

        let mut concepts_val = BTreeSet::new();
        for ms in (0..context.attributes.len()).powerset() {
            let sub: BitSet = ms.into_iter().collect();
            let hull = context.index_attribute_hull(&sub);
            if sub == hull {
                concepts_val.insert(hull);
            }
        }
        assert_eq!(concepts, concepts_val);
    }

    #[test]
    fn test_data_3() {
        let context =
            FormalContext::<String>::from(&fs::read("test_data/data_from_paper.cxt").unwrap())
                .unwrap();

        let concepts: BTreeSet<_> = index_fcbo_concepts(&context).map(|(_, x)| x).collect();

        let mut concepts_val = BTreeSet::new();
        for ms in (0..context.attributes.len()).powerset() {
            let sub: BitSet = ms.into_iter().collect();
            let hull = context.index_attribute_hull(&sub);
            if sub == hull {
                concepts_val.insert(hull);
            }
        }
        assert_eq!(concepts, concepts_val);
    }

    fn next_closure_intents(ctx: &FormalContext<usize>) -> BTreeSet<BitSet> {
        use crate::algorithms::next_closure::index_next_closure_concepts;
        index_next_closure_concepts(ctx).map(|(_, ms)| ms).collect()
    }

    #[test]
    fn test_fcbo_zero_objects() {
        // 5 attributes, 0 objects
        let mut ctx = FormalContext::<usize>::new();
        for m in 0..5 {
            ctx.add_attribute(m, &BitSet::new());
        }
        let fcbo: BTreeSet<_> = index_fcbo_concepts(&ctx).map(|(_, ms)| ms).collect();
        assert_eq!(fcbo, next_closure_intents(&ctx));
    }

    #[test]
    fn test_fcbo_zero_attributes() {
        // 5 objects, 0 attributes
        let mut ctx = FormalContext::<usize>::new();
        for g in 0..5 {
            ctx.add_object(g, &BitSet::new());
        }
        let fcbo: BTreeSet<_> = index_fcbo_concepts(&ctx).map(|(_, ms)| ms).collect();
        assert_eq!(fcbo, next_closure_intents(&ctx));
    }

    #[test]
    fn test_fcbo_single_object_full() {
        let mut ctx = FormalContext::<usize>::new();
        for m in 0..5 {
            ctx.add_attribute(m, &BitSet::new());
        }
        ctx.add_object(0, &(0..5).collect::<BitSet>());
        let fcbo: BTreeSet<_> = index_fcbo_concepts(&ctx).map(|(_, ms)| ms).collect();
        assert_eq!(fcbo, next_closure_intents(&ctx));
    }

    #[test]
    fn test_fcbo_full_context() {
        let mut ctx = FormalContext::<usize>::new();
        for m in 0..5 {
            ctx.add_attribute(m, &BitSet::new());
        }
        for g in 0..5 {
            ctx.add_object(g, &(0..5).collect::<BitSet>());
        }
        let fcbo: BTreeSet<_> = index_fcbo_concepts(&ctx).map(|(_, ms)| ms).collect();
        assert_eq!(fcbo, next_closure_intents(&ctx));
    }

    #[test]
    fn test_fcbo_random_20x20() {
        use rand::{Rng, SeedableRng};
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let n = 20;
        let mut ctx = FormalContext::<usize>::new();
        for m in 0..n {
            ctx.add_attribute(m, &BitSet::new());
        }
        for g in 0..n {
            let intent: BitSet = (0..n).filter(|_| rng.gen::<bool>()).collect();
            ctx.add_object(g, &intent);
        }
        let fcbo: BTreeSet<_> = index_fcbo_concepts(&ctx).map(|(_, ms)| ms).collect();
        assert_eq!(fcbo, next_closure_intents(&ctx));
    }
}
