//  COLLECTIONS.rs
//    by Tim Müller
//
//  Description:
//!   Implements a so-called `HashableMap`, which is exactly like a HashMap but with some performance traded in for determinism in some cases.
//!   
//!   
//!   # Installation
//!   To use this library in your Rust project, simply add it to your `Cargo.toml` file:
//!   ```toml
//!   [dependencies]
//!   hashable-map = { git = "https://github.com/Lut99/hashable-map-rs" }
//!   ```
//!   
//!   Optionally, you can commit to a specific version:
//!   ```toml
//!   [dependencies]
//!   hashable-map = { git = "https://github.com/Lut99/hashable-map-rs", tag = "v0.1.0" }
//!   ```
//!   
//!   You can enable features with the `features`-key:
//!   ```toml
//!   [dependencies]
//!   hashable-map = { git = "https://github.com/Lut99/hashable-map-rs", features = ["serde"] }
//!   ```
//!   
//!   
//!   # Usage
//!   The only type exported by this crate is the `HashableMap` type. It wraps a normal `HashMap` nearly transparently, except for a few changes:
//!   - The HashableMap implements `Hash`. It does so by first ordering the keys by their `Ord`-implementation, then hashing the keys & values in that order. This will provide a map- and `RandomState`-independent fixed ordering that makes the hashes the same.
//!   - In the same way, the library provides variants of `iter()`- `keys()`- and `values()`-functions ending in `_fixed` that always iterate in the order determined by the key's `Ord`-implementation.
//!   
//!   For example, showing the equal hashes:
//!   ```rust
//!   use std::hash::{DefaultHasher, Hash, Hasher as _};
//!   use hashable_map::HashableMap;
//!   
//!   fn hash_one<T: Hash>(elem: T) -> u64 {
//!       let mut hasher = DefaultHasher::new();
//!       elem.hash(&mut hasher);
//!       hasher.finish()
//!   }
//!   
//!   
//!   // Do it multiple times to catch determinism issues!
//!   let contents = [(0, "foo"), (1, "bar"), (2, "baz")];
//!   for _ in 0..100 {
//!       let map1 = HashableMap::from(contents);
//!       let map2 = HashableMap::from(contents);
//!       assert_eq!(hash_one(map1), hash_one(map2));
//!   }
//!   ```
//!   
//!   Or the consistent ordering:
//!   ```rust
//!   use hashable_map::HashableMap;
//!   
//!   // Do it multiple times to hope to catch determinism issues
//!   let map = HashableMap::from([(0, "foo"), (1, "bar"), (2, "baz")]);
//!   for _ in 0..100 {
//!       let mut iter = map.iter_fixed();
//!       assert_eq!(iter.next(), Some((&0, &"foo")));
//!       assert_eq!(iter.next(), Some((&1, &"bar")));
//!       assert_eq!(iter.next(), Some((&2, &"baz")));
//!       assert_eq!(iter.next(), None);
//!   }
//!   ```
//!   
//!   ## Features
//!   The project has the following feature flags:
//!   - `ast-toolkit`: Enables a `Spanning`-implementation from the [`ast-toolkit`](https://github.com/Lut99/ast-toolkit-rs)-crate on the `HashableMap`.
//!   - `serde`: Enables a `Serialize`- and `Deserialize`-implementation on the `HashableMap`. They will always serialize in the order indicated by `K`.
//!     
//!     For example:
//!     ```rust
//!     # #[cfg(feature = "serde")]
//!     # {
//!     use hashable_map::HashableMap;
//!   
//!     // Do it multiple times to hope to catch determinism issues
//!     let map = HashableMap::from([(0, "foo"), (1, "bar"), (2, "baz")]);
//!     for _ in 0..100 {
//!         let smap = serde_json::to_string_pretty(&map).unwrap();
//!         assert_eq!(smap, r#"{
//!       "0": "foo",
//!       "1": "bar",
//!       "2": "baz"
//!     }"#);
//!     }
//!     # }
//!     ```
//!   
//!   
//!   # Contribution
//!   Feel free to contribute to this crate by [raising an issue](https://github.com/Lut99/hashable-map-rs/issues) or [creating a pull request](https://github.com/Lut99/hashable-map-rs/pulls).
//!   
//!   
//!   # License
//!   This project is licensed under the Apache 2.0 license. See [`LICENSE`](./LICENSE) for more information.
//

// Imports
#[cfg(feature = "ast-toolkit")]
use std::borrow::Cow;
use std::collections::HashMap;
use std::hash::{BuildHasher, Hash, Hasher, RandomState};
use std::ops::{Deref, DerefMut};

#[cfg(feature = "ast-toolkit")]
use ast_toolkit::span::{Span, Spannable, Spanning};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};


/***** LIBRARY *****/
/// Wrapper around a classic [`HashMap`] such that it implements [`Hash`].
///
/// The algorithm to hash is based around the idea to hash elements individually first, order their
/// hashes, and then hash them as a whole. This should produce an equal hash but then one which
/// does not rely on the actual order of elements.
#[derive(Clone, Debug)]
pub struct HashableMap<K, V, R = RandomState>(HashMap<K, V, R>);

// Constructors
impl<K, V, R: Default> Default for HashableMap<K, V, R> {
    #[inline]
    fn default() -> Self { Self(Default::default()) }
}
impl<K, V> HashableMap<K, V, RandomState> {
    /// Constructor for an empty HashableMap.
    ///
    /// # Returns
    /// A new HashableMap that has no elements.
    #[inline]
    pub fn new() -> Self { Self(HashMap::new()) }

    /// Constructor for an empty HashableMap that can accept some elements without re-allocation.
    ///
    /// # Arguments
    /// - `capacity`: The number of elements to _at least_ allocate space for. See
    ///   [`HashMap::with_capacity()`] for more details.
    ///
    /// # Returns
    /// A new HashableMap that has no elements but can [`HashableMap::insert()`] at least
    /// `capacity` ones before needing to re-allocate.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self { Self(HashMap::with_capacity(capacity)) }
}
impl<K, V, R> HashableMap<K, V, R> {
    /// Constructor for an empty HashableMap with custom `R`andom state.
    ///
    /// # Arguments
    /// - `state`: Some `R`andom state to create new hashers with.
    ///
    /// # Returns
    /// A new HashableMap that has no elements but is initialized with the given random state.
    #[inline]
    pub const fn with_hasher(state: R) -> Self { Self(HashMap::with_hasher(state)) }

    /// Constructor for an empty HashableMap that can accept some elements without re-allocation
    /// and takes a custom `R`andom state.
    ///
    /// # Arguments
    /// - `capacity`: The number of elements to _at least_ allocate space for. See
    ///   [`HashMap::with_capacity()`] for more details.
    /// - `state`: Some `R`andom state to create new hashers with.
    ///
    /// # Returns
    /// A new HashableMap that has no elements but can [`HashableMap::insert()`] at least
    /// `capacity` ones before needing to re-allocate.
    #[inline]
    pub fn with_capacity_and_hasher(capacity: usize, state: R) -> Self { Self(HashMap::with_capacity_and_hasher(capacity, state)) }
}

// Ops
impl<K, V, R> Deref for HashableMap<K, V, R> {
    type Target = HashMap<K, V, R>;

    #[inline]
    fn deref(&self) -> &Self::Target { &self.0 }
}
impl<K, V, R> DerefMut for HashableMap<K, V, R> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}
impl<K: Eq + Hash, V: Eq, R: BuildHasher> Eq for HashableMap<K, V, R> {}
impl<K: Hash + Ord, V: Hash, R: BuildHasher> Hash for HashableMap<K, V, R> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        // First, collect the items using a predictable order. The order we're using is that
        // determined by the key itself.
        let mut keys: Vec<(&K, &V)> = self.0.iter().collect();
        keys.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));

        // Hash the map in this order
        for (key, value) in keys {
            key.hash(state);
            value.hash(state);
        }
    }
}
impl<K: Eq + Hash, V: PartialEq, R: BuildHasher> PartialEq for HashableMap<K, V, R> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) }
    #[inline]
    fn ne(&self, other: &Self) -> bool { self.0.ne(&other.0) }
}

// Serde
#[cfg(feature = "serde")]
impl<'de, K: Deserialize<'de> + Eq + Hash, V: Deserialize<'de>, R: Default + BuildHasher> Deserialize<'de> for HashableMap<K, V, R> {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Self(HashMap::deserialize(deserializer)?))
    }
}
#[cfg(feature = "serde")]
impl<K: Ord + Serialize, V: Serialize, R> Serialize for HashableMap<K, V, R> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeMap as _;

        // Sort 'em
        let mut pairs: Vec<(&K, &V)> = self.0.iter().collect();
        pairs.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));

        // Serialize 'em
        let mut ser = serializer.serialize_map(Some(pairs.len()))?;
        for (key, value) in pairs {
            ser.serialize_entry(key, value)?;
        }
        ser.end()
    }
}

// Iters
impl<K: Ord, V, R> HashableMap<K, V, R> {
    /// Returns an iterator that returns all keys in the Hashable map as owned keys.
    ///
    /// Note that this function has indeterministic ordering of keys. See
    /// [`HashableMap::into_keys_fixed()`] for a deterministic version.
    ///
    /// # Returns
    /// A [`std::collections::hash_map::IntoKeys`]-iterator that yields keys by ownership.
    #[inline]
    pub fn into_keys(self) -> std::collections::hash_map::IntoKeys<K, V> { self.0.into_keys() }

    /// Returns an iterator that returns all values in the Hashable map as owned values.
    ///
    /// Note that this function has indeterministic ordering of values. See
    /// [`HashableMap::into_values_fixed()`] for a deterministic version.
    ///
    /// # Returns
    /// A [`std::collections::hash_map::IntoValues`]-iterator that yields values by ownership.
    #[inline]
    pub fn into_values(self) -> std::collections::hash_map::IntoValues<K, V> { self.0.into_values() }



    /// Returns an iterator that always iterates in a predictable order.
    ///
    /// Specifically, will do the iteration of the pairs once for you and sorts the result by key.
    /// Then it returns an iterator over that list.
    ///
    /// # Returns
    /// A [`std::vec::IntoIter`] that, despite the type, yields references to keys and values in
    /// the HashableMap. It always iterates in lexigraphical order of the keys.
    #[inline]
    pub fn iter_fixed(&self) -> std::vec::IntoIter<(&K, &V)> {
        let mut pairs: Vec<(&K, &V)> = self.into_iter().collect();
        pairs.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));
        pairs.into_iter()
    }

    /// Returns an iterator that always iterates in a predictable order.
    ///
    /// Specifically, will do the iteration of the pairs once for you and sorts the result by key.
    /// Then it returns an iterator over that list.
    ///
    /// # Returns
    /// A [`std::vec::IntoIter`] that, despite the type, yields readonly references to keys and
    /// mutable references to values in the HashableMap. It always iterates in lexigraphical order
    /// of the keys.
    #[inline]
    pub fn iter_mut_fixed(&mut self) -> std::vec::IntoIter<(&K, &mut V)> {
        let mut pairs: Vec<(&K, &mut V)> = self.into_iter().collect();
        pairs.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));
        pairs.into_iter()
    }

    /// Returns an iterator that always iterates in a predictable order.
    ///
    /// Specifically, will do the iteration of the pairs once for you and sorts the result by key.
    /// Then it returns an iterator over that list.
    ///
    /// # Returns
    /// A [`std::vec::IntoIter`] that yields owned versions of keys and values.
    #[inline]
    pub fn into_iter_fixed(self) -> std::vec::IntoIter<(K, V)> {
        let mut pairs: Vec<(K, V)> = self.into_iter().collect();
        pairs.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));
        pairs.into_iter()
    }



    /// Returns an iterator that always iterates keys in a predictable order.
    ///
    /// Specifically, will do the iteration of the keys once for you and sorts the result. Then it
    /// returns an iterator over that list.
    ///
    /// # Returns
    /// A [`std::vec::IntoIter`] that, despite the type, yields references to keys in the
    /// HashableMap. It always iterates in lexigraphical order of the keys.
    #[inline]
    pub fn keys_fixed(&self) -> std::vec::IntoIter<&K> {
        let mut keys: Vec<&K> = self.keys().collect();
        keys.sort();
        keys.into_iter()
    }

    /// Returns an iterator that always iterates keys in a predictable order.
    ///
    /// Specifically, will do the iteration of the keys once for you and sorts the result. Then it
    /// returns an iterator over that list.
    ///
    /// # Returns
    /// A [`std::vec::IntoIter`] that yields keys in the HashableMap. It always iterates in
    /// lexigraphical order of the keys.
    #[inline]
    pub fn into_keys_fixed(self) -> std::vec::IntoIter<K> {
        let mut keys: Vec<K> = self.0.into_keys().collect();
        keys.sort();
        keys.into_iter()
    }



    /// Returns an iterator that always iterates values in a predictable order.
    ///
    /// Specifically, will do the iteration of the pair once for you and sorts the result by keys.
    /// Then it returns an iterator over that list with only the values.
    ///
    /// # Returns
    /// A [`std::vec::IntoIter`] that, despite the type, yields references to values in the
    /// HashableMap. It always iterates in lexigraphical order of the keys.
    #[inline]
    pub fn values_fixed(&self) -> std::iter::Map<std::vec::IntoIter<(&K, &V)>, for<'a> fn((&'a K, &'a V)) -> &'a V> {
        self.iter_fixed().map(|(_, v)| v)
    }

    /// Returns an iterator that always iterates values in a predictable order.
    ///
    /// Specifically, will do the iteration of the pair once for you and sorts the result by keys.
    /// Then it returns an iterator over that list with only the values.
    ///
    /// # Returns
    /// A [`std::vec::IntoIter`] that, despite the type, yields mutable references to values in the
    /// HashableMap. It always iterates in lexigraphical order of the keys.
    #[inline]
    pub fn values_mut_fixed(&mut self) -> std::iter::Map<std::vec::IntoIter<(&K, &mut V)>, for<'a> fn((&'a K, &'a mut V)) -> &'a mut V> {
        self.iter_mut_fixed().map(|(_, v)| v)
    }

    /// Returns an iterator that always iterates values in a predictable order.
    ///
    /// Specifically, will do the iteration of the pair once for you and sorts the result by keys.
    /// Then it returns an iterator over that list with only the values.
    ///
    /// # Returns
    /// A [`std::vec::IntoIter`] that yields values in the HashableMap. It always iterates in
    /// lexigraphical order of the keys.
    #[inline]
    pub fn into_values_fixed(self) -> std::iter::Map<std::vec::IntoIter<(K, V)>, fn((K, V)) -> V> { self.into_iter_fixed().map(|(_, v)| v) }
}
impl<'a, K, V, R> IntoIterator for &'a HashableMap<K, V, R> {
    type Item = (&'a K, &'a V);
    type IntoIter = std::collections::hash_map::Iter<'a, K, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter { (&self.0).into_iter() }
}
impl<'a, K, V, R> IntoIterator for &'a mut HashableMap<K, V, R> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = std::collections::hash_map::IterMut<'a, K, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter { (&mut self.0).into_iter() }
}
impl<K, V, R> IntoIterator for HashableMap<K, V, R> {
    type Item = (K, V);
    type IntoIter = std::collections::hash_map::IntoIter<K, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter { self.0.into_iter() }
}

// Spanning
#[cfg(feature = "ast-toolkit")]
impl<'s, S: Clone + Spannable<'s>, K, V: Spanning<S>, R> Spanning<S> for HashableMap<K, V, R> {
    #[inline]
    fn get_span(&self) -> Option<Cow<'_, Span<S>>> {
        let mut res: Option<Span<S>> = None;
        for value in self.0.values() {
            match (&mut res, value.get_span()) {
                (Some(res), Some(span)) => {
                    res.extend(span.as_ref());
                },
                (None, Some(span)) => res = Some(span.as_ref().clone()),
                (_, _) => continue,
            }
        }
        res.map(Cow::Owned)
    }

    #[inline]
    fn take_span(self) -> Option<Span<S>> { self.get_span().map(Cow::into_owned) }
}

// Conversion
impl<K: Eq + Hash, V, R2> From<HashMap<K, V, R2>> for HashableMap<K, V, RandomState> {
    #[inline]
    fn from(value: HashMap<K, V, R2>) -> Self { Self::from_iter(value) }
}
impl<const LEN: usize, K: Eq + Hash, V> From<[(K, V); LEN]> for HashableMap<K, V, RandomState> {
    #[inline]
    fn from(value: [(K, V); LEN]) -> Self { Self::from_iter(value) }
}
impl<K: Eq + Hash, V> From<Vec<(K, V)>> for HashableMap<K, V, RandomState> {
    #[inline]
    fn from(value: Vec<(K, V)>) -> Self { Self::from_iter(value) }
}
impl<K: Eq + Hash, V, R: Default + BuildHasher> FromIterator<(K, V)> for HashableMap<K, V, R> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self { Self(HashMap::from_iter(iter)) }
}
