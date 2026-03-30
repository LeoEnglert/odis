//! Core data structures for Formal Concept Analysis.
//!
//! Re-exported at the crate root.
//!
//! - [`formal_context::FormalContext`] — objects × attributes incidence table.
//! - [`lattice::Lattice`] — complete concept lattice (has top and bottom).
//! - [`poset::Poset`] — partially ordered set.
//! - [`iceberg_lattice::IcebergLattice`] — support-filtered concept lattice.
//! - [`drawing::Drawing`] — 2-D coordinate output from a layout algorithm.
//! - [`digraph::Digraph`] — directed graph used internally for layout.

pub mod digraph;
pub mod drawing;
pub mod formal_context;
pub mod iceberg_lattice;
pub mod lattice;
pub mod poset;
