//! Implement a few placeholders for contract attributes until they get implemented upstream.
//! Each tool should implement their own version in a separate module of this crate.

use proc_macro::TokenStream;
use proc_macro_error::proc_macro_error;
use syn::{ItemStruct, parse_macro_input};
use quote::quote;

#[cfg(kani_host)]
#[path = "kani.rs"]
mod tool;

#[cfg(not(kani_host))]
#[path = "runtime.rs"]
mod tool;

#[proc_macro_error]
#[proc_macro_attribute]
pub fn invariant(attr: TokenStream, item: TokenStream) -> TokenStream {
    let safe_body = proc_macro2::TokenStream::from(attr);
    let item = parse_macro_input!(item as ItemStruct);
    let item_name = &item.ident;
    let (impl_generics, ty_generics, where_clause) = item.generics.split_for_impl();

    let expanded = quote! {
        #item
        #[unstable(feature="invariant", issue="none")]
        impl #impl_generics core::ub_checks::Invariant for #item_name #ty_generics #where_clause {
            fn is_safe(&self) -> bool {
                #safe_body
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}

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
