#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] basic_test ["vstd"] => verus_code! {
        fn llama(x: u8) -> (b: bool)
            requires x == 4 || x == 7,
            ensures b == (x == 4)
        {
            x == 4
        }

        fn test() {
            let t = llama;

            let b = t(4);
            assert(b);

            let b = t(7);
            assert(!b);

            assert(forall |x| (x == 4 || x == 7) ==> llama.requires((x,)));
            assert(forall |x, y| llama.ensures((x,), y) ==> x == 4 ==> y);
            assert(forall |x, y| llama.ensures((x,), y) ==> x == 7 ==> !y);
        }

        fn test2() {
            let t = llama;

            let b = t(4);
            assert(!b);     // FAILS
        }

        fn test3() {
            let t = llama;

            t(12); // FAILS
        }

        fn test4() {
            assert(forall |x| (x == 5) ==> llama.requires((x,))); // FAILS
        }

        fn test5() {
            assert(forall |x, y| llama.ensures((x,), y) ==> x == 4 ==> !y); // FAILS
        }

        fn takes_fn1<F: Fn(u8) -> bool>(f: F)
            requires
                f.requires((4,)),
                f.requires((7,)),
                forall |x, y| f.ensures((x,), y) ==> x == 4 ==> y
        {
        }

        fn test_take1() {
            takes_fn1(llama);
        }

        fn takes_fn2<F: Fn(u8) -> bool>(f: F)
            requires
                f.requires((6,)),
        {
        }

        fn test_take2() {
            takes_fn2(llama); // FAILS
        }

        fn takes_fn3<F: Fn(u8) -> bool>(f: F)
            requires
                forall |x, y| f.ensures((x,), y) ==> x == 7 ==> y
        {
        }

        fn test_take3() {
            takes_fn3(llama); // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] generics_test ["vstd"] => verus_code! {
        fn llama<T>(x: T, y: T, z: T) -> (b: bool)
            requires x == y,
            ensures b == (y == z),
        {
            // We can't actually implement this, but it doesn't matter for the test
            assume(false);
            true
        }

        fn test() {
            let t = llama;

            let b = t(4, 4, 6);
            assert(!b);

            let b = t(4, 4, 4);
            assert(b);

            assert(forall |x: u8, y: u8, z: u8| (x == y) ==> llama.requires((x,y,z)));
            assert(forall |x: u8, y: u8, z: u8, b| llama.ensures((x,y,z),b) ==> b == (y == z));
        }

        fn test2() {
            let t = llama;

            let b = t(4, 4, 4);
            assert(!b);     // FAILS
        }

        fn test3() {
            let t = llama;

            t(12, 13, 14); // FAILS
        }

        fn test4() {
            assert(forall |x: u8, y: u8, z: u8| (y == z) ==> llama.requires((x,y,z))); // FAILS
        }

        fn test5() {
            assert(forall |x: u8, y: u8, z: u8, b| llama.ensures((x,y,z),b) ==> b == (y != z)); // FAILS
        }

        struct X { x: u8 }

        fn takes_fn1<F: Fn(X, X, X) -> bool>(f: F)
            requires
                f.requires((X { x: 4 }, X { x: 4 } , X { x: 4 })),
                f.requires((X { x: 7 }, X { x: 7 } , X { x: 4 })),
                forall |x: X, y: X, z: X, b| f.ensures((x,y,z), b) ==> b == (y == z)
        {
        }

        fn test_take1() {
            takes_fn1(llama);
        }

        fn takes_fn2<F: Fn(u8, u8, u8) -> bool>(f: F)
            requires
                f.requires((6,7,8)),
        {
        }

        fn test_take2() {
            takes_fn2(llama); // FAILS
        }

        fn takes_fn3<F: Fn(u8, u8, u8) -> bool>(f: F)
            requires
                forall |x: u8, y: u8, z: u8, b| f.ensures((x,y,z), b) ==> b == (y != z)
        {
        }

        fn test_take3() {
            takes_fn3(llama); // FAILS
        }

        fn takes_fn4<T, F: Fn(T, T, T) -> bool>(f: F)
            requires
                forall |x: T, y: T, z: T, b| f.ensures((x,y,z), b) ==> b == (y != z)
        {
        }

        fn test_take4() {
            takes_fn4(llama::<u8>); // FAILS
        }

    } => Err(err) => assert_fails(err, 7)
}

test_verify_one_file_with_options! {
    #[test] spec_fn_error ["vstd"] => verus_code! {
        spec fn foo() -> bool { true }

        fn test() {
            let x = foo;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use a function as a value unless it as mode 'exec'")
}

test_verify_one_file_with_options! {
    #[test] proof_fn_error ["vstd"] => verus_code! {
        proof fn foo() -> bool { true }

        fn test() {
            let x = foo;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use a function as a value unless it as mode 'exec'")
}

test_verify_one_file_with_options! {
    #[test] mut_params_error ["vstd"] => verus_code! {
        fn stuff(x: &mut u8) { }

        fn test() {
            let x = stuff;
        }
    } => Err(err) => assert_vir_error_msg(err, "not supported: using a function that takes '&mut' params as a value")
}
