// verifast_options{skip_specless_fns}

#![no_std]
#![allow(dead_code)]
#![allow(internal_features)]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(staged_api)]
#![feature(rustc_attrs)]
#![feature(dropck_eyepatch)]
#![feature(specialization)]
#![feature(extend_one)]
#![feature(extend_one_unchecked)]
#![feature(exact_size_is_empty)]
#![feature(trusted_len)]
#![feature(trusted_fused)]
#![feature(try_trait_v2)]
#![feature(pattern)]
#![feature(slice_range)]
#![feature(char_internals)]
#![feature(const_trait_impl)]
#![feature(const_convert)]
#![feature(const_cmp)]
#![feature(const_default)]
#![feature(const_destruct)]
#![feature(const_clone)]
#![feature(const_index)]
#![feature(const_precise_live_drops)]
#![feature(derive_const)]
#![feature(ascii_char)]
#![feature(ascii_char_variants)]
#![feature(clone_to_uninit)]
#![feature(fmt_internals)]
#![feature(formatting_options)]
#![feature(slice_internals)]
#![feature(std_internals)]
#![feature(str_internals)]
#![feature(string_replace_in_place)]
#![feature(unsize)]
#![feature(coerce_unsized)]
#![feature(freeze)]
#![feature(fundamental)]
#![feature(marker_trait_attr)]
#![feature(negative_impls)]
#![feature(deprecated_suggestion)]
#![feature(diagnostic_on_move)]
#![feature(deref_pure_trait)]
#![feature(try_with_capacity)]
#![feature(slice_index_methods)]
#![feature(cast_maybe_uninit)]
#![feature(ptr_cast_array)]
#![feature(iter_advance_by)]
#![feature(unsized_fn_params)]
#![feature(lang_items)]

#![stable(feature = "rust1", since = "1.0.0")]

extern crate alloc as std;

#[stable(feature = "rust1", since = "1.0.0")]
pub use std::alloc as alloc;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::boxed as boxed;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::collections as collections;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::slice as slice;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::vec as vec;

#[stable(feature = "rust1", since = "1.0.0")]
pub mod borrow {
    #[stable(feature = "rust1", since = "1.0.0")]
    pub use core::borrow::{Borrow, BorrowMut};

    #[stable(feature = "rust1", since = "1.0.0")]
    pub trait ToOwned {
        #[stable(feature = "rust1", since = "1.0.0")]
        type Owned: Borrow<Self>;

        #[stable(feature = "rust1", since = "1.0.0")]
        fn to_owned(&self) -> Self::Owned;

        #[stable(feature = "toowned_clone_into", since = "1.63.0")]
        fn clone_into(&self, target: &mut Self::Owned) {
            *target = self.to_owned();
        }
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    pub enum Cow<'a, B: ?Sized + 'a>
    where
        B: ToOwned,
    {
        #[stable(feature = "rust1", since = "1.0.0")]
        Borrowed(#[stable(feature = "rust1", since = "1.0.0")] &'a B),
        #[stable(feature = "rust1", since = "1.0.0")]
        Owned(#[stable(feature = "rust1", since = "1.0.0")] <B as ToOwned>::Owned),
    }

    impl<B: ?Sized + ToOwned> Cow<'_, B> {
        #[stable(feature = "rust1", since = "1.0.0")]
        pub fn into_owned(self) -> <B as ToOwned>::Owned {
            match self {
                Cow::Borrowed(borrowed) => borrowed.to_owned(),
                Cow::Owned(owned) => owned,
            }
        }
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    impl<B: ?Sized + ToOwned> core::ops::Deref for Cow<'_, B>
    where
        B::Owned: Borrow<B>,
    {
        type Target = B;

        fn deref(&self) -> &B {
            match *self {
                Cow::Borrowed(borrowed) => borrowed,
                Cow::Owned(ref owned) => owned.borrow(),
            }
        }
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    impl Borrow<str> for crate::string::String {
        #[inline]
        fn borrow(&self) -> &str {
            &self[..]
        }
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    impl ToOwned for str {
        type Owned = crate::string::String;

        fn to_owned(&self) -> crate::string::String {
            unsafe { crate::string::String::from_utf8_unchecked(self.as_bytes().to_vec()) }
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
pub mod fmt {
    #[stable(feature = "rust1", since = "1.0.0")]
    pub use core::fmt::*;

    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn format(args: Arguments<'_>) -> crate::string::String {
        let mut output = crate::string::String::new();
        let _ = output.write_fmt(args);
        output
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
pub mod str {
    #[stable(feature = "rust1", since = "1.0.0")]
    pub use core::str::*;
    #[stable(feature = "rust1", since = "1.0.0")]
    pub use std::str::from_boxed_utf8_unchecked;

    impl str {
        #[rustc_allow_incoherent_impl]
        #[stable(feature = "rust1", since = "1.0.0")]
        pub fn into_string(self: crate::boxed::Box<Self>) -> crate::string::String {
            let slice = crate::boxed::Box::<[u8]>::from(self);
            unsafe { crate::string::String::from_utf8_unchecked(slice.into_vec()) }
        }
    }
}

pub mod string;
