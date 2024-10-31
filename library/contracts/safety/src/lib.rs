//! Implement a few placeholders for contract attributes until they get implemented upstream.
//! Each tool should implement their own version in a separate module of this crate.

use proc_macro::TokenStream;
use proc_macro_error::proc_macro_error;
use quote::{format_ident, quote, quote_spanned};
use syn::{
    parse_macro_input, parse_quote, spanned::Spanned, Data, DataEnum, DeriveInput, Fields,
    GenericParam, Generics, Ident, Index, ItemStruct,
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
/// This macro is only supported for structs and enums.
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
/// For enums, the body of `is_safe` matches on the variant and calls `is_safe` on its fields,
/// # Example
///
/// ```ignore
/// #[derive(Invariant)]
/// enum MyEnum {
///     OptionOne(u32, u32),
///     OptionTwo(Square),
///     OptionThree
/// }
/// ```
///
/// expands to:
/// ```ignore
/// impl core::ub_checks::Invariant for MyEnum {
///   fn is_safe(&self) -> bool {
///     match self {
///       MyEnum::OptionOne(field1, field2) => field1.is_safe() && field2.is_safe(),
///       MyEnum::OptionTwo(field1) => field1.is_safe(),
///       MyEnum::OptionThree => true,
///     }
///    }
/// }
/// ```
/// For more information on the Invariant trait, see its documentation in core::ub_checks.
#[proc_macro_error]
#[proc_macro_derive(Invariant)]
pub fn derive_invariant(item: TokenStream) -> TokenStream {
    let derive_item = parse_macro_input!(item as DeriveInput);
    let item_name = &derive_item.ident;
    let safe_body = match derive_item.data {
        Data::Struct(struct_data) => {
            safe_body(&struct_data.fields)
        },
        Data::Enum(enum_data) => {
            let variant_checks = variant_checks(enum_data, item_name);

            quote! {
                match self {
                    #(#variant_checks),*
                }
            }
        },
        Data::Union(..) => unimplemented!("Attempted to derive Invariant on a union; Invariant can only be derived for structs and enums."),
    };

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

#[proc_macro_error]
#[proc_macro_attribute]
pub fn loop_invariant(attr: TokenStream, stmt_stream: TokenStream) -> TokenStream {
    tool::loop_invariant(attr, stmt_stream)
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

/// Generate safety checks for each variant of an enum
fn variant_checks(enum_data: DataEnum, item_name: &Ident) -> Vec<proc_macro2::TokenStream> {
    enum_data
        .variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident;
            match &variant.fields {
                Fields::Unnamed(fields) => {
                    let field_names: Vec<_> = fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .map(|(i, _)| format_ident!("field{}", i + 1))
                        .collect();

                    let field_checks: Vec<_> = field_names
                        .iter()
                        .map(|field_name| {
                            quote! { #field_name.is_safe() }
                        })
                        .collect();

                    quote! {
                        #item_name::#variant_name(#(#field_names),*) => #(#field_checks)&&*
                    }
                }
                Fields::Unit => {
                    quote! {
                        #item_name::#variant_name => true
                    }
                }
                Fields::Named(_) => unreachable!("Enums do not have named fields"),
            }
        })
        .collect()
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
