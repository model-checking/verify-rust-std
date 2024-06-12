use proc_macro::TokenStream;

/// For now, runtime requires is a no-op.
///
/// TODO: At runtime the `requires` should become an assert unsafe precondition.
pub(crate) fn requires(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

/// For now, runtime requires is a no-op.
///
/// TODO: At runtime the `ensures` should become an assert as well.
pub(crate) fn ensures(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
