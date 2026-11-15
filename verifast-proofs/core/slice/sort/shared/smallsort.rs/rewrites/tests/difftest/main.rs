// Differential test for rewrites/001: runs the small-sort entry points of original/smallsort.rs (module
// `orig`) and rewritten/smallsort.rs (module `rewr`) on the same inputs and comparators and prints one
// trace per version. The traces must be identical. Built by run.sh in four configurations
// (-C overflow-checks={on,off} x -C debug-assertions={on,off}).
#![allow(internal_features, incomplete_features, dead_code, unexpected_cfgs)]
#![feature(core_intrinsics, freeze, rustc_attrs, specialization)]

use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};

pub use core::{hint, mem, ptr};
pub mod intrinsics {
    pub use core::intrinsics::*;
}
pub mod slice {
    pub use core::slice::*;
    pub mod sort {
        pub mod shared {
            use core::marker::Freeze;
            #[unsafe(rustc_allow_lifetime_dependent_specialization)]
            pub(crate) trait FreezeMarker {}
            impl<T: Freeze> FreezeMarker for T {}
        }
    }
}
mod orig {
    #[path = "../../../../original/smallsort.rs"]
    pub mod smallsort;
}
mod rewr {
    #[path = "../../../../rewritten/smallsort.rs"]
    pub mod smallsort;
}

thread_local! { static DROPS: Cell<u64> = Cell::new(0); }

// A non-Copy, non-Freeze-relevant type with a destructor (counts drops) for the general paths.
#[derive(Clone, Debug, PartialEq)]
struct D(i64, String);
impl Drop for D {
    fn drop(&mut self) { DROPS.with(|d| d.set(d.get() + 1)); }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn below(&mut self, n: u64) -> u64 { self.next() % n }
}

// Comparator kinds: 0 = correct `<`, 1 = random answers, 2 = correct but panics at call `k`,
// 3 = reversed with ties broken randomly (inconsistent).
fn make_cmp<'a, T>(kind: u64, seed: u64, k: u64, key: &'a dyn Fn(&T) -> i64) -> impl FnMut(&T, &T) -> bool + 'a {
    let mut r = Rng(seed | 1);
    let mut calls = 0u64;
    move |a: &T, b: &T| {
        calls += 1;
        match kind {
            0 => key(a) < key(b),
            1 => r.below(2) == 0,
            2 => { if calls == k { panic!("cmp panic") } key(a) < key(b) }
            _ => key(a) > key(b) || (key(a) == key(b) && r.below(2) == 0),
        }
    }
}

macro_rules! run_version {
    ($m:ident, $out:expr, $seed:expr) => {{
        use $m::smallsort as ss;
        let out: &mut Vec<String> = $out;
        let mut rng = Rng($seed);
        for case in 0..4000u64 {
            let len = rng.below(40) as usize;
            let kind = rng.below(4);
            let cs = rng.next();
            let k = rng.below(60);
            let range = 1 + rng.below(20) as i64;
            let ints: Vec<i64> = (0..len).map(|_| rng.below(range as u64) as i64).collect();
            let which = rng.below(4);
            // (a) insertion_sort_shift_left on i64 and on D
            let mut v = ints.clone();
            let offset = if len == 0 { 1 } else { 1 + rng.below(len as u64) as usize };
            let key_i = |x: &i64| *x;
            let r = catch_unwind(AssertUnwindSafe(|| {
                if len >= 1 { ss::insertion_sort_shift_left(&mut v, offset, &mut make_cmp(kind, cs, k, &key_i)); }
            }));
            out.push(format!("{case} isl i64 {:?} {:?}", r.is_ok(), v));
            DROPS.with(|d| d.set(0));
            let mut dv: Vec<D> = ints.iter().map(|&x| D(x, x.to_string())).collect();
            let key_d = |x: &D| x.0;
            let r = catch_unwind(AssertUnwindSafe(|| {
                if len >= 1 { ss::insertion_sort_shift_left(&mut dv, offset, &mut make_cmp(kind, cs, k, &key_d)); }
            }));
            let drops_during = DROPS.with(|d| d.get());
            out.push(format!("{case} isl D {:?} {:?} drops={drops_during}", r.is_ok(), dv.iter().map(|d| (d.0, d.1.clone())).collect::<Vec<_>>()));
            // (b) the three trait small sorts (len <= threshold, as their callers guarantee)
            let mut v2: Vec<i64> = ints.iter().copied().take(32).collect();
            let r = catch_unwind(AssertUnwindSafe(|| match which {
                0 => <i64 as ss::UnstableSmallSortTypeImpl>::small_sort(&mut v2, &mut make_cmp(kind, cs, k, &key_i)),
                1 => <i64 as ss::UnstableSmallSortFreezeTypeImpl>::small_sort(&mut v2, &mut make_cmp(kind, cs, k, &key_i)),
                2 => {
                    let mut scratch: Vec<mem::MaybeUninit<i64>> = Vec::with_capacity(48);
                    unsafe { scratch.set_len(48) };
                    <i64 as ss::StableSmallSortTypeImpl>::small_sort(&mut v2, &mut scratch, &mut make_cmp(kind, cs, k, &key_i))
                }
                _ => {
                    let mut d2: Vec<D> = v2.iter().map(|&x| D(x, String::new())).collect();
                    <D as ss::UnstableSmallSortTypeImpl>::small_sort(&mut d2, &mut make_cmp(kind, cs, k, &key_d));
                    v2 = d2.iter().map(|d| d.0).collect();
                }
            }));
            out.push(format!("{case} ss{which} {:?} {:?}", r.is_ok(), v2));
        }
    }};
}

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut a = Vec::new();
    let mut b = Vec::new();
    run_version!(orig, &mut a, 0x9e3779b97f4a7c15);
    run_version!(rewr, &mut b, 0x9e3779b97f4a7c15);
    let n = a.len();
    let same = a == b;
    for l in &a { println!("{l}"); }
    eprintln!("lines={n} identical={same}");
    if !same { std::process::exit(1); }
}
