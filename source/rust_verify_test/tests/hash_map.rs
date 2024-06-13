#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_hash_map verus_code! {
        use vstd::prelude::*;
        use std::collections::HashMap;
        fn test()
        {
            let mut m = HashMap::<u32, u32>::new();
            assert(m@ == Map::<u32, u32>::empty());

            m.insert(3, 4);
            m.insert(6, 8);
            assert(m@[3] == 4);
            
            let b = m.contains_key(&3);
            assert(b);
            
            let n = m.len();
            assert(n == 2);
            
            let v = m.get(&6);
            match v {
                Some(v) => assert(*v == 8),
                None => assert(false),
            };

            m.clear();
            assert(!m@.contains_key(3));
            let b = m.contains_key(&3);
            assert(!b);
        }
    } => Ok(())
}
