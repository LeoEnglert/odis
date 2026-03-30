use bit_set::BitSet;
use std::io::{self, Write};

use crate::FormalContext;

use super::canonical_basis;

/// Clears the terminal screen.
fn clear_screen() {
    print!("{esc}[2J{esc}[1;1H", esc = 27 as char);
}

/// Asks the user if an implication (premise -> conclusion) is valid.
fn first_question(context: &FormalContext<String>, question: (&BitSet, &BitSet)) -> bool {
    let premise: Vec<String> = question
        .0
        .iter()
        .map(|index| context.attributes[index].to_string())
        .collect();
    let conclusion: Vec<String> = question
        .1
        .iter()
        .map(|index| context.attributes[index].to_string())
        .collect();

    clear_screen();
    loop {
        let mut answer = String::new();

        println!("Is the following implication valid?");
        println!("  {:?} -> {:?}", premise, conclusion);

        print!("Please enter your answer (\"yes\", \"no\"): ");
        io::stdout().flush().unwrap();
        io::stdin().read_line(&mut answer).unwrap();

        clear_screen();

        match answer.trim() {
            "yes" => return true,
            "no" => return false,
            _ => {
                println!("Please only answer with: \"yes\" or \"no\"!\n");
            }
        }
    }
}

/// Asks the user to provide a counterexample (new object name and its attributes).
fn second_question(context: &FormalContext<String>) -> (String, BitSet) {
    clear_screen();

    let mut object = String::new();
    let mut attributes_set = BitSet::new();

    loop {
        object.clear();
        print!("Enter name of new object: ");
        io::stdout().flush().unwrap();
        io::stdin().read_line(&mut object).unwrap();

        clear_screen();

        if object.is_ascii() {
            break;
        } else {
            println!("Please only use ASCII characters.")
        }
    }

    'outer: loop {
        let mut attributes = String::new();
        attributes_set.clear();

        println!("Name all attributes this object possesses.");
        println!("Please use the following format: \"1. attr, 2. attr, 3. attr, ...\"");

        io::stdout().flush().unwrap();
        io::stdin().read_line(&mut attributes).unwrap();

        clear_screen();

        let names: Vec<&str> = attributes
            .trim()
            .split(',')
            .filter_map(|x| {
                let trimmed = x.trim();
                if trimmed.is_empty() {
                    None
                } else {
                    Some(trimmed)
                }
            })
            .collect();

        if names.is_empty() {
            println!("Please enter at least one attribute or leave empty if intentional (logic specific).\n");
            // Assuming user must enter something based on original code trying to loop?
            // Original code: if empty, loop finished without doing anything, broke 'a (success) -> empty set.
            break 'outer;
        }

        for name in names {
            if let Some(index) = context.attributes.iter().position(|r| r.as_str() == name) {
                attributes_set.insert(index);
            } else {
                println!(
                    "Attribute \"{}\" not found. Please only enter valid attribute names.\n",
                    name
                );
                continue 'outer;
            }
        }
        break 'outer;
    }
    object = object.trim().to_string();

    (object, attributes_set)
}

/// Performs attribute exploration algorithm to discover implications.
pub fn index_attribute_exploration(context: &mut FormalContext<String>) -> Vec<(BitSet, BitSet)> {
    let mut basis: Vec<(BitSet, BitSet)> = Vec::new();

    let mut temp_set = BitSet::new();

    let all_attributes: BitSet = (0..context.attributes.len()).collect();

    while temp_set != all_attributes {
        loop {
            let temp_set_hull = context.index_attribute_hull(&temp_set);

            if temp_set == temp_set_hull {
                break;
            }

            if first_question(
                context,
                (&temp_set, &temp_set_hull.difference(&temp_set).collect()),
            ) {
                basis.push((temp_set.clone(), temp_set_hull));

                break;
            } else {
                let (new_object, attributes) = second_question(context);

                context.add_object(new_object, &attributes);
            }
        }

        temp_set = canonical_basis::index_next_preclosure(context, &basis, &temp_set);
    }

    basis
}

/// Callback-based attribute exploration. The callback receives `(premise, conclusion)` BitSets
/// and returns:
/// - `None`  → accept the implication (it holds)
/// - `Some((object_name, attribute_bits))` → reject; add this object as a counterexample
///
/// This allows programmatic exploration without stdin/stdout interaction.
pub fn index_attribute_exploration_with_callback<F>(
    context: &mut FormalContext<String>,
    mut callback: F,
) -> Vec<(BitSet, BitSet)>
where
    F: FnMut(&BitSet, &BitSet) -> Option<(String, BitSet)>,
{
    let mut basis: Vec<(BitSet, BitSet)> = Vec::new();
    let mut temp_set = BitSet::new();
    let all_attributes: BitSet = (0..context.attributes.len()).collect();

    while temp_set != all_attributes {
        loop {
            let temp_set_hull = context.index_attribute_hull(&temp_set);

            if temp_set == temp_set_hull {
                break;
            }

            let conclusion: BitSet = temp_set_hull.difference(&temp_set).collect();
            match callback(&temp_set, &conclusion) {
                None => {
                    basis.push((temp_set.clone(), temp_set_hull));
                    break;
                }
                Some((new_object, attributes)) => {
                    context.add_object(new_object, &attributes);
                }
            }
        }

        temp_set = canonical_basis::index_next_preclosure(context, &basis, &temp_set);
    }

    basis
}
