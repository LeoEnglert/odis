//! Next Closure concept enumeration algorithm.

use bit_set::BitSet;

use crate::FormalContext;

/// Computes the next formal concept in lectic order given an intent `a`.
fn next_concept<T>(context: &FormalContext<T>, a: &BitSet) -> Option<(BitSet, BitSet)> {
    let mut a_new = a.clone();

    // Iterate attributes in reverse order to find the lectic next closure
    for i in (0..context.attributes.len()).rev() {
        if a.contains(i) {
            a_new.remove(i);
        } else {
            let mut b = a_new.clone();
            b.insert(i);
            // Compute closure of b: b''
            let gs = context.index_extent(&b);
            let b_closure = context.index_intent(&gs);

            // Check if new elements in closure are >= i
            // diff = b_closure \ a_new. We want smallest element of diff to be i.
            // Since we just inserted i into b (and thus into b_closure), i is in diff.
            // We need to ensure no j < i is in diff.
            if let Some(min_diff) = b_closure.difference(&a_new).next() {
                if min_diff >= i {
                    return Some((gs, b_closure));
                }
            } else {
                // Should not happen as we inserted i
                // But strictly speaking if b_closure == a_new (impossible as i was not in a_new)
            }
        }
    }

    None
}

/// Returns an iterator over all formal concepts of the context using Next Closure algorithm.
pub fn index_next_closure_concepts<'a, T>(
    context: &'a FormalContext<T>,
) -> impl Iterator<Item = (BitSet, BitSet)> + 'a {
    // First concept is the closure of empty set of attributes
    let gs = context.index_extent(&BitSet::new());
    let ms = context.index_intent(&gs);
    let mut next = Some((gs, ms));

    std::iter::from_fn(move || {
        if let Some((g, m)) = next.clone() {
            next = next_concept(context, &m);
            Some((g, m))
        } else {
            None
        }
    })
}

/// Zero-size handle for the Next Closure concept enumeration algorithm.
pub struct NextClosure;

impl<T> crate::traits::ConceptEnumerator<T> for NextClosure {
    fn enumerate_concepts<'ctx>(
        &self,
        context: &'ctx crate::FormalContext<T>,
    ) -> impl Iterator<Item = (BitSet, BitSet)> + 'ctx {
        index_next_closure_concepts(context)
    }
}

#[cfg(test)]
mod tests {
    use crate::{algorithms::next_closure::index_next_closure_concepts, FormalContext};
    use bit_set::BitSet;
    use itertools::Itertools;
    use std::{collections::BTreeSet, fs};

    #[test]
    fn test_concepts() {
        let context = FormalContext::<String>::from(
            &fs::read("test_data/living_beings_and_water.cxt").unwrap(),
        )
        .unwrap();

        let concepts: BTreeSet<_> = index_next_closure_concepts(&context).map(|(_, x)| x).collect();
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

    fn brute_force_concept_intents(ctx: &FormalContext<usize>) -> BTreeSet<BitSet> {
        let mut result = BTreeSet::new();
        for ms in (0..ctx.attributes.len()).powerset() {
            let sub: BitSet = ms.into_iter().collect();
            let hull = ctx.index_attribute_hull(&sub);
            if sub == hull {
                result.insert(hull);
            }
        }
        result
    }

    fn build_context(n_attrs: usize, incidences: &[(usize, usize)]) -> FormalContext<usize> {
        let n_objs = incidences.iter().map(|&(g, _)| g).max().map_or(0, |m| m + 1);
        let mut ctx = FormalContext::<usize>::new();
        for m in 0..n_attrs {
            ctx.add_attribute(m, &BitSet::new());
        }
        for g in 0..n_objs {
            let intent: BitSet = incidences.iter().filter(|&&(og, _)| og == g).map(|&(_, m)| m).collect();
            ctx.add_object(g, &intent);
        }
        ctx
    }

    #[test]
    fn test_concepts_zero_objects() {
        // 5 attributes, 0 objects: only the top concept (∅, M)
        let mut ctx = FormalContext::<usize>::new();
        for m in 0..5 {
            ctx.add_attribute(m, &BitSet::new());
        }
        let concepts: Vec<_> = index_next_closure_concepts(&ctx).collect();
        assert_eq!(concepts.len(), 1);
        assert!(concepts[0].0.is_empty(), "extent must be empty");
        assert_eq!(concepts[0].1, (0..5).collect::<BitSet>(), "intent must be M");
    }

    #[test]
    fn test_concepts_zero_attributes() {
        // 5 objects, 0 attributes: only the bottom concept (G, ∅)
        let mut ctx = FormalContext::<usize>::new();
        for g in 0..5 {
            ctx.add_object(g, &BitSet::new());
        }
        let concepts: Vec<_> = index_next_closure_concepts(&ctx).collect();
        assert_eq!(concepts.len(), 1);
        assert_eq!(concepts[0].0, (0..5).collect::<BitSet>(), "extent must be G");
        assert!(concepts[0].1.is_empty(), "intent must be empty");
    }

    #[test]
    fn test_concepts_single_object_full() {
        // 1 object with all 5 attributes
        let mut ctx = FormalContext::<usize>::new();
        for m in 0..5 {
            ctx.add_attribute(m, &BitSet::new());
        }
        let full_intent: BitSet = (0..5).collect();
        ctx.add_object(0, &full_intent);
        let intents: BTreeSet<_> = index_next_closure_concepts(&ctx).map(|(_, ms)| ms).collect();
        assert_eq!(intents, brute_force_concept_intents(&ctx));
    }

    #[test]
    fn test_concepts_full_context() {
        // 5×5 full context: all incidences = 1
        let incidences: Vec<(usize, usize)> = (0..5).flat_map(|g| (0..5).map(move |m| (g, m))).collect();
        let ctx = build_context(5, &incidences);
        let intents: BTreeSet<_> = index_next_closure_concepts(&ctx).map(|(_, ms)| ms).collect();
        assert_eq!(intents, brute_force_concept_intents(&ctx));
    }

    #[test]
    fn test_concepts_random_20x20() {
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
        let intents: BTreeSet<_> = index_next_closure_concepts(&ctx).map(|(_, ms)| ms).collect();
        assert_eq!(intents, brute_force_concept_intents(&ctx));
    }
}
