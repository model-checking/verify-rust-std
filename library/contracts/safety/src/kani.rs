use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{parse_macro_input, ItemFn};

pub(crate) fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    rewrite_attr(attr, item, "requires")
}

pub(crate) fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    rewrite_attr(attr, item, "ensures")
}

fn rewrite_attr(attr: TokenStream, item: TokenStream, name: &str) -> TokenStream {
    let args = proc_macro2::TokenStream::from(attr);
    let fn_item = parse_macro_input!(item as ItemFn);
    let attribute = format_ident!("{}", name);
    quote!(
        #[kani_core::#attribute(#args)]
        #fn_item
    )
    .into()
}
