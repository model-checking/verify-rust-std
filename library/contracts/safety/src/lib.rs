//! Implement a few placeholders for contract attributes until they get implemented upstream.
//! Each tool should implement their own version in a separate module of this crate.

use proc_macro::TokenStream;
use proc_macro_error::proc_macro_error;

#[cfg(kani_host)]
#[path = "kani.rs"]
mod tool;

#[cfg(not(kani_host))]
#[path = "runtime.rs"]
mod tool;

#[proc_macro_error]
#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    tool::requires(attr, item)
}

#[proc_macro_error]
#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    tool::ensures(attr, item)
}

#[proc_macro_error]
#[proc_macro_attribute]
pub fn loop_invariant(attr: TokenStream, stmt_stream: TokenStream) -> TokenStream {
    tool::loop_invariant(attr, stmt_stream)
}
