//! Bidirectional multimap implementation.

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

/// Bidirectional multimap.
///
/// This maps keys to sets of values, and a corresponding key can be looked up
/// for each value. Each value has a unique corresponding key. The sets of
/// values are disjoint.
#[derive(Clone, Debug)]
pub struct BiMulMap<K, V> {
    forward: HashMap<K, HashSet<V>>,
    backward: HashMap<V, K>,
}

impl<K, V> Default for BiMulMap<K, V> {
    fn default() -> Self {
        Self {
            forward: HashMap::new(),
            backward: HashMap::new(),
        }
    }
}

impl<K, V> BiMulMap<K, V> {
    /// Construct a new [`BiMulMap`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the number of key-value pairs in the map.
    pub fn len(&self) -> usize {
        self.forward.len()
    }

    /// Returns whether the map is empty.
    pub fn is_empty(&self) -> bool {
        self.forward.is_empty()
    }
}

impl<K, V> BiMulMap<K, V>
where
    K: Eq + Hash + Clone,
    V: Eq + Hash + Clone,
{
    /// Inserts a key-value pair into the map. If the value was already mapped
    /// under a different key, it is moved to the new key's bucket so that the
    /// disjoint-buckets invariant is preserved.
    pub fn insert(&mut self, key: K, value: V) {
        // If the value is already mapped, pull it out of its current bucket
        // first (unless it's already under `key`, in which case we're done).
        if let Some(existing) = self.backward.get(&value) {
            if *existing == key {
                return;
            }
            let old_key = existing.clone();
            if let Some(set) = self.forward.get_mut(&old_key) {
                set.remove(&value);
                if set.is_empty() {
                    self.forward.remove(&old_key);
                }
            }
        }
        self.forward
            .entry(key.clone())
            .or_default()
            .insert(value.clone());
        self.backward.insert(value, key);
    }

    /// Get the key corresponding to a value.
    pub fn get_key(&self, value: &V) -> Option<&K> {
        self.backward.get(value)
    }

    /// Get the set of values corresponding to a key.
    pub fn get_values(&self, key: &K) -> Option<&HashSet<V>> {
        self.forward.get(key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Verify the forward/backward consistency invariant for every entry:
    /// `backward[v] == k` iff `v ∈ forward[k]`, and no value appears under
    /// more than one key (the buckets are disjoint).
    fn assert_consistent<K, V>(m: &BiMulMap<K, V>)
    where
        K: Eq + Hash + std::fmt::Debug,
        V: Eq + Hash + std::fmt::Debug,
    {
        // Every forward entry is reflected in backward, and buckets are disjoint.
        let mut seen_values: HashSet<&V> = HashSet::new();
        for (k, values) in &m.forward {
            assert!(
                !values.is_empty(),
                "empty bucket left in forward for key {k:?}"
            );
            for v in values {
                assert_eq!(
                    m.backward.get(v),
                    Some(k),
                    "forward has ({k:?}, {v:?}) but backward disagrees"
                );
                assert!(
                    seen_values.insert(v),
                    "value {v:?} appears in multiple forward buckets"
                );
            }
        }
        // Every backward entry is reflected in forward.
        for (v, k) in &m.backward {
            let set = m
                .forward
                .get(k)
                .unwrap_or_else(|| panic!("backward maps {v:?} to {k:?} with no forward bucket"));
            assert!(
                set.contains(v),
                "backward maps {v:?} to {k:?} but value missing from forward bucket"
            );
        }
        assert_eq!(
            m.forward.values().map(|s| s.len()).sum::<usize>(),
            m.backward.len(),
            "forward total size disagrees with backward size"
        );
    }

    #[test]
    fn fresh_insert_is_visible_in_both_directions() {
        let mut m: BiMulMap<u32, &'static str> = BiMulMap::new();
        m.insert(1, "a");
        assert_eq!(m.get_key(&"a"), Some(&1));
        assert!(m.get_values(&1).unwrap().contains("a"));
        assert_consistent(&m);
    }

    #[test]
    fn one_key_holds_many_values() {
        let mut m: BiMulMap<u32, &'static str> = BiMulMap::new();
        m.insert(1, "a");
        m.insert(1, "b");
        m.insert(1, "c");
        let values = m.get_values(&1).unwrap();
        assert_eq!(values.len(), 3);
        for v in ["a", "b", "c"] {
            assert!(values.contains(v));
            assert_eq!(m.get_key(&v), Some(&1));
        }
        assert_eq!(m.len(), 1);
        assert_consistent(&m);
    }

    #[test]
    fn reinserting_value_under_new_key_moves_it() {
        let mut m: BiMulMap<u32, &'static str> = BiMulMap::new();
        m.insert(1, "a");
        m.insert(1, "b");
        m.insert(2, "a"); // move "a" from 1 to 2
        assert_eq!(m.get_key(&"a"), Some(&2));
        assert!(!m.get_values(&1).unwrap().contains("a"));
        assert!(m.get_values(&2).unwrap().contains("a"));
        assert_eq!(m.get_values(&1).unwrap().len(), 1); // just "b"
        assert_consistent(&m);
    }

    #[test]
    fn reinserting_same_pair_is_idempotent() {
        let mut m: BiMulMap<u32, &'static str> = BiMulMap::new();
        m.insert(1, "a");
        m.insert(1, "a");
        m.insert(1, "a");
        assert_eq!(m.get_values(&1).unwrap().len(), 1);
        assert_eq!(m.get_key(&"a"), Some(&1));
        assert_consistent(&m);
    }

    #[test]
    fn moving_last_value_drops_empty_bucket() {
        let mut m: BiMulMap<u32, &'static str> = BiMulMap::new();
        m.insert(1, "a");
        m.insert(2, "a"); // 1's bucket should now be gone
        assert!(m.get_values(&1).is_none());
        assert_eq!(m.len(), 1);
        assert_consistent(&m);
    }

    #[test]
    fn distinct_keys_hold_disjoint_values() {
        let mut m: BiMulMap<u32, &'static str> = BiMulMap::new();
        m.insert(1, "a");
        m.insert(1, "b");
        m.insert(2, "c");
        m.insert(2, "d");
        assert_eq!(m.len(), 2);
        assert_eq!(m.get_key(&"a"), Some(&1));
        assert_eq!(m.get_key(&"b"), Some(&1));
        assert_eq!(m.get_key(&"c"), Some(&2));
        assert_eq!(m.get_key(&"d"), Some(&2));
        assert_consistent(&m);
    }

    #[test]
    fn missing_lookups_return_none() {
        let mut m: BiMulMap<u32, &'static str> = BiMulMap::new();
        assert!(m.is_empty());
        assert_eq!(m.get_key(&"nope"), None);
        assert!(m.get_values(&42).is_none());
        m.insert(1, "a");
        assert_eq!(m.get_key(&"other"), None);
        assert!(m.get_values(&99).is_none());
    }
}
