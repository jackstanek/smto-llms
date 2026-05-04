//! Random name selection for story generation

use rand::{self, Rng, seq::IndexedRandom};

mod inner {
    include!(concat!(env!("OUT_DIR"), "/names.rs"));
}

/// Genders for names
pub enum NameGender {
    Male,
    Female,
}

/// Select a random name
pub fn random_name<R>(rng: &mut R, gender: NameGender) -> &'static str
where
    R: Rng,
{
    let namelist = if let NameGender::Male = gender {
        inner::MALE_NAMES
    } else {
        inner::FEMALE_NAMES
    };
    namelist.choose(rng).expect("male names empty")
}

/// Get a gender-balanced list of n names.
pub fn random_balanced_names<R>(rng: &mut R, n: usize) -> Vec<&'static str>
where
    R: Rng,
{
    let n_males = n / 2;
    let mut names = Vec::with_capacity(n);
    for _ in 0..n_males {
        names.push(random_name(rng, NameGender::Male));
    }
    for _ in n_males..n {
        names.push(random_name(rng, NameGender::Female));
    }
    names
}
