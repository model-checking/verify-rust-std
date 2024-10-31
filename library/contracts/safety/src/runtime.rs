use proc_macro::TokenStream;

/// For now, runtime requires is a no-op.
///
/// TODO: At runtime the `requires` should become an assert unsafe precondition.
pub(crate) fn requires(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

/// For now, runtime ensures is a no-op.
///
/// TODO: At runtime the `ensures` should become an assert as well.
pub(crate) fn ensures(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

/// For now, runtime loop_invariant is a no-op.
///
/// TODO: At runtime the `loop_invariant` should become an assert as well.
pub(crate) fn loop_invariant(_attr: TokenStream, stmt_stream: TokenStream) -> TokenStream {
    stmt_stream
}
