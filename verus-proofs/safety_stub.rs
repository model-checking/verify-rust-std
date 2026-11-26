// Stand-in for `library/contracts/safety` outside Kani, where `requires` and
// `loop_invariant` return the item unchanged (see its `runtime.rs`).
extern crate proc_macro;
use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn requires(_attr: TokenStream, item: TokenStream) -> TokenStream { item }

#[proc_macro_attribute]
pub fn loop_invariant(_attr: TokenStream, item: TokenStream) -> TokenStream { item }
