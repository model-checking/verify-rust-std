//! Implement a few placeholders for contract attributes until they get implemented upstream.
//! Each tool should implement their own version in a separate module of this crate.

use proc_macro::TokenStream;
use proc_macro_error::proc_macro_error;
use quote::{quote, quote_spanned};
use syn::{
    parse_macro_input, parse_quote, spanned::Spanned, Data, DeriveInput, Fields, GenericParam,
    Generics, Index, ItemStruct,
};

#[cfg(kani_host)]
#[path = "kani.rs"]
mod tool;

#[cfg(not(kani_host))]
#[path = "runtime.rs"]
mod tool;

/// Expands the `#[invariant(...)]` attribute macro.
/// The macro expands to an implementation of the `is_safe` method for the `Invariant` trait.
/// This attribute is only supported for structs.
///
/// # Example
///
/// ```ignore
/// #[invariant(self.width == self.height)]
/// struct Square {
///     width: u32,
///     height: u32,
/// }
/// ```
/// 
/// expands to:
/// ```ignore
/// impl core::ub_checks::Invariant for Square {
///   fn is_safe(&self) -> bool {
///     self.width == self.height
///   }
/// }
/// ```
/// For more information on the Invariant trait, see its documentation in core::ub_checks.
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

/// Expands the derive macro for the Invariant trait.
/// The macro expands to an implementation of the `is_safe` method for the `Invariant` trait.
/// This macro is only supported for structs.
///
/// # Example
///
/// ```ignore
/// #[derive(Invariant)]
/// struct Square {
///     width: u32,
///     height: u32,
/// }
/// ```
/// 
/// expands to:
/// ```ignore
/// impl core::ub_checks::Invariant for Square {
///   fn is_safe(&self) -> bool {
///     self.width.is_safe() && self.height.is_safe()
///   }
/// }
/// ```
/// For more information on the Invariant trait, see its documentation in core::ub_checks.
#[proc_macro_error]
#[proc_macro_derive(Invariant)]
pub fn derive_invariant(item: TokenStream) -> TokenStream {
    let derive_item = parse_macro_input!(item as DeriveInput);
    let item_name = &derive_item.ident;
    if let Data::Struct(struct_data) = derive_item.data {
        let safe_body = safe_body(&struct_data.fields);

        // Add a bound `T: Invariant` to every type parameter T.
        let generics = add_trait_bound_invariant(derive_item.generics);
        // Generate an expression to sum up the heap size of each field.
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let expanded = quote! {
            // The generated implementation.
            #[unstable(feature="invariant", issue="none")]
            impl #impl_generics core::ub_checks::Invariant for #item_name #ty_generics #where_clause {
                fn is_safe(&self) -> bool {
                    #safe_body
                }
            }
        };
        proc_macro::TokenStream::from(expanded)
    } else {
        panic!("Attempted to derive the Invariant trait on a non-struct type.")
    }
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

/// Add a bound `T: Invariant` to every type parameter T.
fn add_trait_bound_invariant(mut generics: Generics) -> Generics {
    generics.params.iter_mut().for_each(|param| {
        if let GenericParam::Type(type_param) = param {
            type_param
                .bounds
                .push(parse_quote!(core::ub_checks::Invariant));
        }
    });
    generics
}

/// Generate the body for the `is_safe` method.
/// For each field of the type, enforce that it is safe.
fn safe_body(fields: &Fields) -> proc_macro2::TokenStream {
    match fields {
        Fields::Named(ref fields) => {
            let field_safe_calls: Vec<proc_macro2::TokenStream> = fields
                .named
                .iter()
                .map(|field| {
                    let name = &field.ident;
                    quote_spanned! {field.span()=>
                        self.#name.is_safe()
                    }
                })
                .collect();
            if !field_safe_calls.is_empty() {
                quote! { #( #field_safe_calls )&&* }
            } else {
                quote! { true }
            }
        }
        Fields::Unnamed(ref fields) => {
            let field_safe_calls: Vec<proc_macro2::TokenStream> = fields
                .unnamed
                .iter()
                .enumerate()
                .map(|(idx, field)| {
                    let field_idx = Index::from(idx);
                    quote_spanned! {field.span()=>
                        self.#field_idx.is_safe()
                    }
                })
                .collect();
            if !field_safe_calls.is_empty() {
                quote! { #( #field_safe_calls )&&* }
            } else {
                quote! { true }
            }
        }
        Fields::Unit => quote! { true },
    }
}
