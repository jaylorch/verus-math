use super::super::prelude::*;
use builtin::*;

use core::option::Option;
use core::option::Option::None;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash, Hasher};

verus! {

#[verifier::external_body]
pub spec fn hash_state_to_u64<T: ?Sized>(s: Seq<Seq<u8>>) -> u64;

#[verifier::external_body]
pub spec fn hasher_view<T: ?Sized>(h: &T) -> Seq<Seq<u8>>;

#[verifier::external_trait_specification]
#[verifier::external_body]
pub trait ExHasher {
    type ExternalTraitSpecificationFor: Hasher;

    fn finish(&self) -> (result: u64)
        ensures
            result == hash_state_to_u64::<Self>(hasher_view(self));
}

#[verifier::external_body]
pub spec fn can_be_hashed_to_bytes<T: ?Sized>() -> bool;

#[verifier::external_body]
pub spec fn hash_to_bytes<T: ?Sized>(x: &T) -> Seq<u8>
    recommends
        can_be_hashed_to_bytes::<T>();

#[verifier::external_trait_specification]
pub trait ExHash {
    type ExternalTraitSpecificationFor: Hash;

    fn hash<HasherT>(&self, state: &mut HasherT)
        where
            HasherT: Hasher,
        ensures
            can_be_hashed_to_bytes::<Self>() ==>
                hasher_view(state) == hasher_view(old::<&mut _>(state)).push(hash_to_bytes(self));
}

#[verifier::external_trait_specification]
pub trait ExBuildHasher {
    type ExternalTraitSpecificationFor: BuildHasher;
    type Hasher: Hasher;

    fn build_hasher(&self) -> (result: <Self as ExBuildHasher>::Hasher)
        ensures
            hasher_view(&result) == Seq::<Seq<u8>>::empty();

    fn hash_one<T>(&self, x: T) -> (result: u64)
        where
            Self: ExBuildHasher + Sized,
            T: Hash,
        ensures
            can_be_hashed_to_bytes::<T>() ==>
                result == hash_state_to_u64::<Self::Hasher>(Seq::empty().push(hash_to_bytes(&x)));
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(Key)]
#[verifier::reject_recursive_types(Value)]
#[verifier::reject_recursive_types(S)]
pub struct ExHashMap<Key, Value, S>(HashMap<Key, Value, S>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRandomState(std::collections::hash_map::RandomState);

pub trait HashMapAdditionalSpecFns<Key, Value>: View<V = Map<Key, Value>> {
    spec fn spec_index(&self, k: Key) -> Value
        recommends
            self.view().contains_key(k),
    ;
}

impl<Key, Value, S> HashMapAdditionalSpecFns<Key, Value> for HashMap<Key, Value, S> {
    #[verifier::inline]
    open spec fn spec_index(&self, k: Key) -> Value {
        self.view().index(k)
    }
}

impl<Key, Value, S> View for HashMap<Key, Value, S>
{
    type V = Map<Key, Value>;

    #[verifier::external_body]
    closed spec fn view(&self) -> Map<Key, Value>;
}

////// Len (with autospec)
pub open spec fn spec_hash_map_len<Key, Value, S>(v: &HashMap<Key, Value, S>) -> usize;

// This axiom is slightly better than defining spec_hash_map_len to just be `m@.len() as usize`
// (the axiom also shows that m@.len() is in-bounds for usize)
pub broadcast proof fn axiom_spec_len<Key, Value, S>(m: &HashMap<Key, Value, S>)
    ensures
        #[trigger] spec_hash_map_len(m) == m@.len(),
{
    admit();
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(spec_hash_map_len)]
pub fn ex_hash_map_len<Key, Value, S>(m: &HashMap<Key, Value, S>) -> (len: usize)
    ensures
        len == spec_hash_map_len(m),
{
    m.len()
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_new<Key, Value>() -> (m: HashMap<Key, Value>)
    ensures
        m@ == Map::<Key, Value>::empty(),
{
    HashMap::<Key, Value>::new()
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_with_capacity<Key, Value>(capacity: usize) -> (m: HashMap<Key, Value>)
    ensures
        m@ == Map::<Key, Value>::empty(),
{
    HashMap::<Key, Value>::with_capacity(capacity)
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_reserve<Key, Value, S>(m: &mut HashMap<Key, Value, S>, additional: usize)
    where
        Key: Eq + Hash,
        S: BuildHasher,
    ensures
        m@ == old(m)@,
{
    m.reserve(additional)
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_insert<Key, Value, S>(m: &mut HashMap<Key, Value, S>, k: Key, v: Value) -> (result: Option<Value>)
    where
        Key: Eq + Hash,
        S: BuildHasher,
    ensures
        m@ == old(m)@.insert(k, v),
        match result {
            Some(v) => old(m)@.contains_key(k) && v == old(m)[k],
            None => !old(m)@.contains_key(k),
        },
{
    m.insert(k, v)
}

pub spec fn map_contains_borrowed_key<Key, Value, Q>(m: Map<Key, Value>, k: &Q) -> bool
    where
        Key: Borrow<Q> + Hash + Eq,
        Q: Hash + Eq + ?Sized;

pub broadcast proof fn axiom_map_contains_borrowed_key<Key, Value>(m: Map<Key, Value>, k: &Key)
    where
        Key: Hash + Eq,
    ensures
        #[trigger] map_contains_borrowed_key::<Key, Value, Key>(m, k) <==> m.contains_key(*k)
{
    admit();
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_contains_key<Key, Value, S, Q>(m: &HashMap<Key, Value, S>, k: &Q) -> (result: bool)
    where
        Key: Borrow<Q> + Hash + Eq,
        Q: Hash + Eq + ?Sized,
        S: BuildHasher,
    ensures
        result == map_contains_borrowed_key(m@, k),
{
    m.contains_key(k)
}

pub spec fn map_maps_borrowed_key_to_value<Key, Value, Q>(m: Map<Key, Value>, k: &Q, v: Value) -> bool
    where
        Key: Borrow<Q> + Hash + Eq,
        Q: Hash + Eq + ?Sized;

pub broadcast proof fn axiom_map_maps_borrowed_key_to_value<Key, Value>(m: Map<Key, Value>, k: &Key, v: Value)
    where
        Key: Hash + Eq,
    ensures
        #[trigger] map_maps_borrowed_key_to_value::<Key, Value, Key>(m, k, v) <==> m.contains_key(*k) && m[*k] == v
{
    admit();
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_get<'a, Key, Value, S, Q>(m: &'a HashMap<Key, Value, S>, k: &Q) -> (result: Option<&'a Value>)
    where
        Key: Borrow<Q> + Hash + Eq,
        Q: Hash + Eq + ?Sized,
        S: BuildHasher,
    ensures
        match result {
            Some(v) => map_maps_borrowed_key_to_value(m@, k, *v),
            None => !map_contains_borrowed_key(m@, k),
        },
{
    m.get(k)
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_clear<Key, Value, S>(m: &mut HashMap<Key, Value, S>)
    ensures
        m@ == Map::<Key, Value>::empty(),
{
    m.clear()
}

}
