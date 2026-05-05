//! Random name selection for story generation

use rand::{Rng, seq::IndexedRandom};

mod inner {
    include!(concat!(env!("OUT_DIR"), "/names_inner.rs"));
}

/// Get a gender-balanced list of n names.
pub(crate) fn random_balanced_names<R>(rng: &mut R, n: usize) -> Vec<&'static str>
where
    R: Rng,
{
    let n_males = n / 2;
    let mut names = Vec::with_capacity(n);
    names.extend(inner::MALE_NAMES.sample(rng, n_males));
    names.extend(inner::FEMALE_NAMES.sample(rng, n - n_males));
    names
}
