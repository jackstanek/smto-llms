//! Tools for generating lists of departments.

use rand::{Rng, seq::IndexedRandom};

const DEPARTMENTS: &[&'static str] = &[
    "Engineering",
    "Human Resources",
    "Finance",
    "Marketing",
    "Legal",
    "Sales",
    "Product Management",
    "Customer Support",
    "Research & Development",
    "Operations",
];

/// Get a random list of departments.
pub fn random_balanced_names<R>(rng: &mut R, n: usize) -> Vec<&'static str>
where
    R: Rng,
{
    let mut recv = Vec::with_capacity(n);
    recv.extend(DEPARTMENTS.sample(rng, n));
    recv
}
