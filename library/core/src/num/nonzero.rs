//! Definitions of integer that is known not to equal zero.

use safety::{ensures, requires};

use super::{IntErrorKind, ParseIntError};
use crate::clone::{TrivialClone, UseCloned};
use crate::cmp::Ordering;
use crate::hash::{Hash, Hasher};
#[cfg(kani)]
use crate::kani;
use crate::marker::{Destruct, Freeze, StructuralPartialEq};
use crate::ops::{BitOr, BitOrAssign, Div, DivAssign, Neg, Rem, RemAssign};
use crate::panic::{RefUnwindSafe, UnwindSafe};
use crate::str::FromStr;
use crate::{fmt, intrinsics, ptr, ub_checks};

/// A marker trait for primitive types which can be zero.
///
/// This is an implementation detail for <code>[NonZero]\<T></code> which may disappear or be replaced at any time.
///
/// # Safety
///
/// Types implementing this trait must be primitives that are valid when zeroed.
///
/// The associated `Self::NonZeroInner` type must have the same size+align as `Self`,
/// but with a niche and bit validity making it so the following `transmutes` are sound:
///
/// - `Self::NonZeroInner` to `Option<Self::NonZeroInner>`
/// - `Option<Self::NonZeroInner>` to `Self`
///
/// (And, consequently, `Self::NonZeroInner` to `Self`.)
#[unstable(
    feature = "nonzero_internals",
    reason = "implementation detail which may disappear or be replaced at any time",
    issue = "none"
)]
pub unsafe trait ZeroablePrimitive: Sized + Copy + private::Sealed {
    #[doc(hidden)]
    type NonZeroInner: Sized + Copy;
}

macro_rules! impl_zeroable_primitive {
    ($($NonZeroInner:ident ( $primitive:ty )),+ $(,)?) => {
        mod private {
            #[unstable(
                feature = "nonzero_internals",
                reason = "implementation detail which may disappear or be replaced at any time",
                issue = "none"
            )]
            pub trait Sealed {}
        }

        $(
            #[unstable(
                feature = "nonzero_internals",
                reason = "implementation detail which may disappear or be replaced at any time",
                issue = "none"
            )]
            impl private::Sealed for $primitive {}

            #[unstable(
                feature = "nonzero_internals",
                reason = "implementation detail which may disappear or be replaced at any time",
                issue = "none"
            )]
            unsafe impl ZeroablePrimitive for $primitive {
                type NonZeroInner = super::niche_types::$NonZeroInner;
            }
        )+
    };
}

impl_zeroable_primitive!(
    NonZeroU8Inner(u8),
    NonZeroU16Inner(u16),
    NonZeroU32Inner(u32),
    NonZeroU64Inner(u64),
    NonZeroU128Inner(u128),
    NonZeroUsizeInner(usize),
    NonZeroI8Inner(i8),
    NonZeroI16Inner(i16),
    NonZeroI32Inner(i32),
    NonZeroI64Inner(i64),
    NonZeroI128Inner(i128),
    NonZeroIsizeInner(isize),
    NonZeroCharInner(char),
);

/// A value that is known not to equal zero.
///
/// This enables some memory layout optimization.
/// For example, `Option<NonZero<u32>>` is the same size as `u32`:
///
/// ```
/// use core::{num::NonZero};
///
/// assert_eq!(size_of::<Option<NonZero<u32>>>(), size_of::<u32>());
/// ```
///
/// # Layout
///
/// `NonZero<T>` is guaranteed to have the same layout and bit validity as `T`
/// with the exception that the all-zero bit pattern is invalid.
/// `Option<NonZero<T>>` is guaranteed to be compatible with `T`, including in
/// FFI.
///
/// Thanks to the [null pointer optimization], `NonZero<T>` and
/// `Option<NonZero<T>>` are guaranteed to have the same size and alignment:
///
/// ```
/// use std::num::NonZero;
///
/// assert_eq!(size_of::<NonZero<u32>>(), size_of::<Option<NonZero<u32>>>());
/// assert_eq!(align_of::<NonZero<u32>>(), align_of::<Option<NonZero<u32>>>());
/// ```
///
/// [null pointer optimization]: crate::option#representation
///
/// # Note on generic usage
///
/// `NonZero<T>` can only be used with some standard library primitive types
/// (such as `u8`, `i32`, and etc.). The type parameter `T` must implement the
/// internal trait [`ZeroablePrimitive`], which is currently permanently unstable
/// and cannot be implemented by users. Therefore, you cannot use `NonZero<T>`
/// with your own types, nor can you implement traits for all `NonZero<T>`,
/// only for concrete types.
#[stable(feature = "generic_nonzero", since = "1.79.0")]
#[repr(transparent)]
#[rustc_nonnull_optimization_guaranteed]
#[rustc_diagnostic_item = "NonZero"]
pub struct NonZero<T: ZeroablePrimitive>(T::NonZeroInner);

macro_rules! impl_nonzero_fmt {
    ($(#[$Attribute:meta] $Trait:ident)*) => {
        $(
            #[$Attribute]
            impl<T> fmt::$Trait for NonZero<T>
            where
                T: ZeroablePrimitive + fmt::$Trait,
            {
                #[inline]
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    self.get().fmt(f)
                }
            }
        )*
    };
}

impl_nonzero_fmt! {
    #[stable(feature = "nonzero", since = "1.28.0")]
    Debug
    #[stable(feature = "nonzero", since = "1.28.0")]
    Display
    #[stable(feature = "nonzero", since = "1.28.0")]
    Binary
    #[stable(feature = "nonzero", since = "1.28.0")]
    Octal
    #[stable(feature = "nonzero", since = "1.28.0")]
    LowerHex
    #[stable(feature = "nonzero", since = "1.28.0")]
    UpperHex
    #[stable(feature = "nonzero_fmt_exp", since = "1.84.0")]
    LowerExp
    #[stable(feature = "nonzero_fmt_exp", since = "1.84.0")]
    UpperExp
}

macro_rules! impl_nonzero_auto_trait {
    (unsafe $Trait:ident) => {
        #[stable(feature = "nonzero", since = "1.28.0")]
        unsafe impl<T> $Trait for NonZero<T> where T: ZeroablePrimitive + $Trait {}
    };
    ($Trait:ident) => {
        #[stable(feature = "nonzero", since = "1.28.0")]
        impl<T> $Trait for NonZero<T> where T: ZeroablePrimitive + $Trait {}
    };
}

// Implement auto-traits manually based on `T` to avoid docs exposing
// the `ZeroablePrimitive::NonZeroInner` implementation detail.
impl_nonzero_auto_trait!(unsafe Freeze);
impl_nonzero_auto_trait!(RefUnwindSafe);
impl_nonzero_auto_trait!(unsafe Send);
impl_nonzero_auto_trait!(unsafe Sync);
impl_nonzero_auto_trait!(Unpin);
impl_nonzero_auto_trait!(UnwindSafe);

#[stable(feature = "nonzero", since = "1.28.0")]
impl<T> Clone for NonZero<T>
where
    T: ZeroablePrimitive,
{
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

#[unstable(feature = "ergonomic_clones", issue = "132290")]
impl<T> UseCloned for NonZero<T> where T: ZeroablePrimitive {}

#[stable(feature = "nonzero", since = "1.28.0")]
impl<T> Copy for NonZero<T> where T: ZeroablePrimitive {}

#[doc(hidden)]
#[unstable(feature = "trivial_clone", issue = "none")]
unsafe impl<T> TrivialClone for NonZero<T> where T: ZeroablePrimitive {}

#[stable(feature = "nonzero", since = "1.28.0")]
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
impl<T> const PartialEq for NonZero<T>
where
    T: ZeroablePrimitive + [const] PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }

    #[inline]
    fn ne(&self, other: &Self) -> bool {
        self.get() != other.get()
    }
}

#[unstable(feature = "structural_match", issue = "31434")]
impl<T> StructuralPartialEq for NonZero<T> where T: ZeroablePrimitive + StructuralPartialEq {}

#[stable(feature = "nonzero", since = "1.28.0")]
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
impl<T> const Eq for NonZero<T> where T: ZeroablePrimitive + [const] Eq {}

#[stable(feature = "nonzero", since = "1.28.0")]
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
impl<T> const PartialOrd for NonZero<T>
where
    T: ZeroablePrimitive + [const] PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.get().partial_cmp(&other.get())
    }

    #[inline]
    fn lt(&self, other: &Self) -> bool {
        self.get() < other.get()
    }

    #[inline]
    fn le(&self, other: &Self) -> bool {
        self.get() <= other.get()
    }

    #[inline]
    fn gt(&self, other: &Self) -> bool {
        self.get() > other.get()
    }

    #[inline]
    fn ge(&self, other: &Self) -> bool {
        self.get() >= other.get()
    }
}

#[stable(feature = "nonzero", since = "1.28.0")]
#[rustc_const_unstable(feature = "const_cmp", issue = "143800")]
impl<T> const Ord for NonZero<T>
where
    // FIXME(const_hack): the T: ~const Destruct should be inferred from the Self: ~const Destruct.
    // See https://github.com/rust-lang/rust/issues/144207
    T: ZeroablePrimitive + [const] Ord + [const] Destruct,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.get().cmp(&other.get())
    }

    #[inline]
    fn max(self, other: Self) -> Self {
        // SAFETY: The maximum of two non-zero values is still non-zero.
        unsafe { Self::new_unchecked(self.get().max(other.get())) }
    }

    #[inline]
    fn min(self, other: Self) -> Self {
        // SAFETY: The minimum of two non-zero values is still non-zero.
        unsafe { Self::new_unchecked(self.get().min(other.get())) }
    }

    #[inline]
    fn clamp(self, min: Self, max: Self) -> Self {
        // SAFETY: A non-zero value clamped between two non-zero values is still non-zero.
        unsafe { Self::new_unchecked(self.get().clamp(min.get(), max.get())) }
    }
}

#[stable(feature = "nonzero", since = "1.28.0")]
impl<T> Hash for NonZero<T>
where
    T: ZeroablePrimitive + Hash,
{
    #[inline]
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.get().hash(state)
    }
}

#[stable(feature = "from_nonzero", since = "1.31.0")]
#[rustc_const_unstable(feature = "const_convert", issue = "143773")]
impl<T> const From<NonZero<T>> for T
where
    T: ZeroablePrimitive,
{
    #[inline]
    fn from(nonzero: NonZero<T>) -> Self {
        // Call `get` method to keep range information.
        nonzero.get()
    }
}

#[stable(feature = "nonzero_bitor", since = "1.45.0")]
#[rustc_const_unstable(feature = "const_ops", issue = "143802")]
impl<T> const BitOr for NonZero<T>
where
    T: ZeroablePrimitive + [const] BitOr<Output = T>,
{
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        // SAFETY: Bitwise OR of two non-zero values is still non-zero.
        unsafe { Self::new_unchecked(self.get() | rhs.get()) }
    }
}

#[stable(feature = "nonzero_bitor", since = "1.45.0")]
#[rustc_const_unstable(feature = "const_ops", issue = "143802")]
impl<T> const BitOr<T> for NonZero<T>
where
    T: ZeroablePrimitive + [const] BitOr<Output = T>,
{
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: T) -> Self::Output {
        // SAFETY: Bitwise OR of a non-zero value with anything is still non-zero.
        unsafe { Self::new_unchecked(self.get() | rhs) }
    }
}

#[stable(feature = "nonzero_bitor", since = "1.45.0")]
#[rustc_const_unstable(feature = "const_ops", issue = "143802")]
impl<T> const BitOr<NonZero<T>> for T
where
    T: ZeroablePrimitive + [const] BitOr<Output = T>,
{
    type Output = NonZero<T>;

    #[inline]
    fn bitor(self, rhs: NonZero<T>) -> Self::Output {
        // SAFETY: Bitwise OR of anything with a non-zero value is still non-zero.
        unsafe { NonZero::new_unchecked(self | rhs.get()) }
    }
}

#[stable(feature = "nonzero_bitor", since = "1.45.0")]
#[rustc_const_unstable(feature = "const_ops", issue = "143802")]
impl<T> const BitOrAssign for NonZero<T>
where
    T: ZeroablePrimitive,
    Self: [const] BitOr<Output = Self>,
{
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

#[stable(feature = "nonzero_bitor", since = "1.45.0")]
#[rustc_const_unstable(feature = "const_ops", issue = "143802")]
impl<T> const BitOrAssign<T> for NonZero<T>
where
    T: ZeroablePrimitive,
    Self: [const] BitOr<T, Output = Self>,
{
    #[inline]
    fn bitor_assign(&mut self, rhs: T) {
        *self = *self | rhs;
    }
}

impl<T> NonZero<T>
where
    T: ZeroablePrimitive,
{
    /// Creates a non-zero if the given value is not zero.
    #[stable(feature = "nonzero", since = "1.28.0")]
    #[rustc_const_stable(feature = "const_nonzero_int_methods", since = "1.47.0")]
    #[must_use]
    #[inline]
    #[ensures(|result: &Option<Self>| {
        let size = core::mem::size_of::<T>();
        // Layout precondition backing the body's `transmute_unchecked`.
        let layout_ok = size == core::mem::size_of::<Option<Self>>();
        // Read `n` as raw bytes to reason about "is zero" generically over `T`.
        let n_ptr: *const T = &n;
        let n_slice = unsafe { core::slice::from_raw_parts(n_ptr as *const u8, size) };
        let n_is_zero = n_slice.iter().all(|&byte| byte == 0);
        // (2a) A `NonZero` is produced if and only if the input was nonzero.
        let created_iff_nonzero = result.is_some() == !n_is_zero;
        // (2b) When produced, the inner value equals the input `n`.
        let value_preserved = match result {
            Some(nz) => {
                let inner: T = nz.get();
                let inner_ptr: *const T = &inner;
                let inner_slice =
                    unsafe { core::slice::from_raw_parts(inner_ptr as *const u8, size) };
                n_slice == inner_slice
            }
            None => true,
        };
        layout_ok && created_iff_nonzero && value_preserved
    })]
    pub const fn new(n: T) -> Option<Self> {
        // SAFETY: Memory layout optimization guarantees that `Option<NonZero<T>>` has
        //         the same layout and size as `T`, with `0` representing `None`.
        unsafe { intrinsics::transmute_unchecked(n) }
    }

    /// Creates a non-zero without checking whether the value is non-zero.
    /// This results in undefined behavior if the value is zero.
    ///
    /// # Safety
    ///
    /// The value must not be zero.
    #[stable(feature = "nonzero", since = "1.28.0")]
    #[rustc_const_stable(feature = "nonzero", since = "1.28.0")]
    #[must_use]
    #[inline]
    #[track_caller]
    // `NonZero::new` performs the canonical zero test via the niche layout
    // (`Option<NonZero<T>>` has the same layout as `T`, with 0 as `None`),
    // and `raw_eq` compares the object representations directly. Both are
    // single operations for the verifier. Spelling these clauses as raw
    // byte-slice inspections instead (as done previously) makes every
    // asserted occurrence of this contract pay for symbolic pointer
    // indirection and iterator reasoning, which dominated verification time
    // of harnesses whose call graph contains NonZero constructions.
    #[requires(NonZero::new(n).is_some())]
    #[ensures(|result: &Self| unsafe { core::intrinsics::raw_eq(&result.get(), &n) })]
    pub const unsafe fn new_unchecked(n: T) -> Self {
        match Self::new(n) {
            Some(n) => n,
            None => {
                // SAFETY: The caller guarantees that `n` is non-zero, so this is unreachable.
                unsafe {
                    ub_checks::assert_unsafe_precondition!(
                        check_language_ub,
                        "NonZero::new_unchecked requires the argument to be non-zero",
                        () => false,
                    );
                    intrinsics::unreachable()
                }
            }
        }
    }

    /// Converts a reference to a non-zero mutable reference
    /// if the referenced value is not zero.
    #[unstable(feature = "nonzero_from_mut", issue = "106290")]
    #[must_use]
    #[inline]
    pub fn from_mut(n: &mut T) -> Option<&mut Self> {
        // SAFETY: Memory layout optimization guarantees that `Option<NonZero<T>>` has
        //         the same layout and size as `T`, with `0` representing `None`.
        let opt_n = unsafe { &mut *(ptr::from_mut(n).cast::<Option<Self>>()) };

        opt_n.as_mut()
    }

    /// Converts a mutable reference to a non-zero mutable reference
    /// without checking whether the referenced value is non-zero.
    /// This results in undefined behavior if the referenced value is zero.
    ///
    /// # Safety
    ///
    /// The referenced value must not be zero.
    #[unstable(feature = "nonzero_from_mut", issue = "106290")]
    #[must_use]
    #[inline]
    #[track_caller]
    // See new_unchecked: the niche-layout zero test is much cheaper for the
    // verifier than inspecting the object representation byte by byte.
    #[requires(NonZero::new(*n).is_some())]
    pub unsafe fn from_mut_unchecked(n: &mut T) -> &mut Self {
        match Self::from_mut(n) {
            Some(n) => n,
            None => {
                // SAFETY: The caller guarantees that `n` references a value that is non-zero, so this is unreachable.
                unsafe {
                    ub_checks::assert_unsafe_precondition!(
                        check_library_ub,
                        "NonZero::from_mut_unchecked requires the argument to dereference as non-zero",
                        () => false,
                    );
                    intrinsics::unreachable()
                }
            }
        }
    }

    /// Returns the contained value as a primitive type.
    #[stable(feature = "nonzero", since = "1.28.0")]
    #[rustc_const_stable(feature = "const_nonzero_get", since = "1.34.0")]
    #[inline]
    pub const fn get(self) -> T {
        // Rustc can set range metadata only if it loads `self` from
        // memory somewhere. If the value of `self` was from by-value argument
        // of some not-inlined function, LLVM don't have range metadata
        // to understand that the value cannot be zero.
        //
        // Using the transmute `assume`s the range at runtime.
        //
        // Even once LLVM supports `!range` metadata for function arguments
        // (see <https://github.com/llvm/llvm-project/issues/76628>), this can't
        // be `.0` because MCP#807 bans field-projecting into `scalar_valid_range`
        // types, and it arguably wouldn't want to be anyway because if this is
        // MIR-inlined, there's no opportunity to put that argument metadata anywhere.
        //
        // The good answer here will eventually be pattern types, which will hopefully
        // allow it to go back to `.0`, maybe with a cast of some sort.
        //
        // SAFETY: `ZeroablePrimitive` guarantees that the size and bit validity
        // of `.0` is such that this transmute is sound.
        unsafe { intrinsics::transmute_unchecked(self) }
    }
}

macro_rules! nonzero_integer {
    (
        #[$stability:meta]
        Self = $Ty:ident,
        Primitive = $signedness:ident $Int:ident,
        SignedPrimitive = $Sint:ty,
        UnsignedPrimitive = $Uint:ty,

        // Used in doc comments.
        rot = $rot:literal,
        rot_op = $rot_op:literal,
        rot_result = $rot_result:literal,
        swap_op = $swap_op:literal,
        swapped = $swapped:literal,
        reversed = $reversed:literal,
        leading_zeros_test = $leading_zeros_test:expr,
    ) => {
        #[doc = sign_dependent_expr!{
            $signedness ?
            if signed {
                concat!("An [`", stringify!($Int), "`] that is known not to equal zero.")
            }
            if unsigned {
                concat!("A [`", stringify!($Int), "`] that is known not to equal zero.")
            }
        }]
        ///
        /// This enables some memory layout optimization.
        #[doc = concat!("For example, `Option<", stringify!($Ty), ">` is the same size as `", stringify!($Int), "`:")]
        ///
        /// ```rust
        #[doc = concat!("assert_eq!(size_of::<Option<core::num::", stringify!($Ty), ">>(), size_of::<", stringify!($Int), ">());")]
        /// ```
        ///
        /// # Layout
        ///
        #[doc = concat!("`", stringify!($Ty), "` is guaranteed to have the same layout and bit validity as `", stringify!($Int), "`")]
        /// with the exception that `0` is not a valid instance.
        #[doc = concat!("`Option<", stringify!($Ty), ">` is guaranteed to be compatible with `", stringify!($Int), "`,")]
        /// including in FFI.
        ///
        /// Thanks to the [null pointer optimization],
        #[doc = concat!("`", stringify!($Ty), "` and `Option<", stringify!($Ty), ">`")]
        /// are guaranteed to have the same size and alignment:
        ///
        /// ```
        #[doc = concat!("use std::num::", stringify!($Ty), ";")]
        ///
        #[doc = concat!("assert_eq!(size_of::<", stringify!($Ty), ">(), size_of::<Option<", stringify!($Ty), ">>());")]
        #[doc = concat!("assert_eq!(align_of::<", stringify!($Ty), ">(), align_of::<Option<", stringify!($Ty), ">>());")]
        /// ```
        ///
        /// # Compile-time creation
        ///
        /// Since both [`Option::unwrap()`] and [`Option::expect()`] are `const`, it is possible to
        /// define a new
        #[doc = concat!("`", stringify!($Ty), "`")]
        /// at compile time via:
        /// ```
        #[doc = concat!("use std::num::", stringify!($Ty), ";")]
        ///
        #[doc = concat!("const TEN: ", stringify!($Ty), " = ", stringify!($Ty) , r#"::new(10).expect("ten is non-zero");"#)]
        /// ```
        ///
        /// [null pointer optimization]: crate::option#representation
        #[$stability]
        pub type $Ty = NonZero<$Int>;

        impl NonZero<$Int> {
            /// The size of this non-zero integer type in bits.
            ///
            #[doc = concat!("This value is equal to [`", stringify!($Int), "::BITS`].")]
            ///
            /// # Examples
            ///
            /// ```
            /// # use std::num::NonZero;
            /// #
            #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::BITS, ", stringify!($Int), "::BITS);")]
            /// ```
            #[stable(feature = "nonzero_bits", since = "1.67.0")]
            pub const BITS: u32 = <$Int>::BITS;

            /// Returns the number of leading zeros in the binary representation of `self`.
            ///
            /// On many architectures, this function can perform better than `leading_zeros()` on the underlying integer type, as special handling of zero can be avoided.
            ///
            /// # Examples
            ///
            /// ```
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let n = NonZero::<", stringify!($Int), ">::new(", $leading_zeros_test, ")?;")]
            ///
            /// assert_eq!(n.leading_zeros(), 0);
            /// # Some(())
            /// # }
            /// ```
            #[stable(feature = "nonzero_leading_trailing_zeros", since = "1.53.0")]
            #[rustc_const_stable(feature = "nonzero_leading_trailing_zeros", since = "1.53.0")]
            #[must_use = "this returns the result of the operation, \
                          without modifying the original"]
            #[inline]
            pub const fn leading_zeros(self) -> u32 {
                // SAFETY: since `self` cannot be zero, it is safe to call `ctlz_nonzero`.
                unsafe {
                    intrinsics::ctlz_nonzero(self.get() as $Uint)
                }
            }

            /// Returns the number of trailing zeros in the binary representation
            /// of `self`.
            ///
            /// On many architectures, this function can perform better than `trailing_zeros()` on the underlying integer type, as special handling of zero can be avoided.
            ///
            /// # Examples
            ///
            /// ```
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let n = NonZero::<", stringify!($Int), ">::new(0b0101000)?;")]
            ///
            /// assert_eq!(n.trailing_zeros(), 3);
            /// # Some(())
            /// # }
            /// ```
            #[stable(feature = "nonzero_leading_trailing_zeros", since = "1.53.0")]
            #[rustc_const_stable(feature = "nonzero_leading_trailing_zeros", since = "1.53.0")]
            #[must_use = "this returns the result of the operation, \
                          without modifying the original"]
            #[inline]
            pub const fn trailing_zeros(self) -> u32 {
                // SAFETY: since `self` cannot be zero, it is safe to call `cttz_nonzero`.
                unsafe {
                    intrinsics::cttz_nonzero(self.get() as $Uint)
                }
            }

            /// Returns `self` with only the most significant bit set.
            ///
            /// # Example
            ///
            /// ```
            /// #![feature(isolate_most_least_significant_one)]
            ///
            /// # use core::num::NonZero;
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let a = NonZero::<", stringify!($Int), ">::new(0b_01100100)?;")]
            #[doc = concat!("let b = NonZero::<", stringify!($Int), ">::new(0b_01000000)?;")]
            ///
            /// assert_eq!(a.isolate_highest_one(), b);
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "isolate_most_least_significant_one", issue = "136909")]
            #[must_use = "this returns the result of the operation, \
                        without modifying the original"]
            #[inline(always)]
            pub const fn isolate_highest_one(self) -> Self {
                // SAFETY:
                // `self` is non-zero, so masking to preserve only the most
                // significant set bit will result in a non-zero `n`.
                // and self.leading_zeros() is always < $INT::BITS since
                // at least one of the bits in the number is not zero
                unsafe {
                    let bit = (((1 as $Uint) << (<$Uint>::BITS - 1)).unchecked_shr(self.leading_zeros()));
                    NonZero::new_unchecked(bit as $Int)
                }
            }

            /// Returns `self` with only the least significant bit set.
            ///
            /// # Example
            ///
            /// ```
            /// #![feature(isolate_most_least_significant_one)]
            ///
            /// # use core::num::NonZero;
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let a = NonZero::<", stringify!($Int), ">::new(0b_01100100)?;")]
            #[doc = concat!("let b = NonZero::<", stringify!($Int), ">::new(0b_00000100)?;")]
            ///
            /// assert_eq!(a.isolate_lowest_one(), b);
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "isolate_most_least_significant_one", issue = "136909")]
            #[must_use = "this returns the result of the operation, \
                        without modifying the original"]
            #[inline(always)]
            pub const fn isolate_lowest_one(self) -> Self {
                let n = self.get();
                let n = n & n.wrapping_neg();

                // SAFETY: `self` is non-zero, so `self` with only its least
                // significant set bit will remain non-zero.
                unsafe { NonZero::new_unchecked(n) }
            }

            /// Returns the index of the highest bit set to one in `self`.
            ///
            /// # Examples
            ///
            /// ```
            /// #![feature(int_lowest_highest_one)]
            ///
            /// # use core::num::NonZero;
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::new(0b1)?.highest_one(), 0);")]
            #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::new(0b1_0000)?.highest_one(), 4);")]
            #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::new(0b1_1111)?.highest_one(), 4);")]
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "int_lowest_highest_one", issue = "145203")]
            #[must_use = "this returns the result of the operation, \
                          without modifying the original"]
            #[inline(always)]
            pub const fn highest_one(self) -> u32 {
                Self::BITS - 1 - self.leading_zeros()
            }

            /// Returns the index of the lowest bit set to one in `self`.
            ///
            /// # Examples
            ///
            /// ```
            /// #![feature(int_lowest_highest_one)]
            ///
            /// # use core::num::NonZero;
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::new(0b1)?.lowest_one(), 0);")]
            #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::new(0b1_0000)?.lowest_one(), 4);")]
            #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::new(0b1_1111)?.lowest_one(), 0);")]
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "int_lowest_highest_one", issue = "145203")]
            #[must_use = "this returns the result of the operation, \
                          without modifying the original"]
            #[inline(always)]
            pub const fn lowest_one(self) -> u32 {
                self.trailing_zeros()
            }

            /// Returns the number of ones in the binary representation of `self`.
            ///
            /// # Examples
            ///
            /// ```
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let a = NonZero::<", stringify!($Int), ">::new(0b100_0000)?;")]
            #[doc = concat!("let b = NonZero::<", stringify!($Int), ">::new(0b100_0011)?;")]
            ///
            /// assert_eq!(a.count_ones(), NonZero::new(1)?);
            /// assert_eq!(b.count_ones(), NonZero::new(3)?);
            /// # Some(())
            /// # }
            /// ```
            ///
            #[stable(feature = "non_zero_count_ones", since = "1.86.0")]
            #[rustc_const_stable(feature = "non_zero_count_ones", since = "1.86.0")]
            #[doc(alias = "popcount")]
            #[doc(alias = "popcnt")]
            #[must_use = "this returns the result of the operation, \
                        without modifying the original"]
            #[inline(always)]
            #[ensures(|result| result.get() > 0)]
            pub const fn count_ones(self) -> NonZero<u32> {
                // SAFETY:
                // `self` is non-zero, which means it has at least one bit set, which means
                // that the result of `count_ones` is non-zero.
                unsafe { NonZero::new_unchecked(self.get().count_ones()) }
            }

            /// Shifts the bits to the left by a specified amount, `n`,
            /// wrapping the truncated bits to the end of the resulting integer.
            ///
            /// Please note this isn't the same operation as the `<<` shifting operator!
            ///
            /// # Examples
            ///
            /// ```
            /// #![feature(nonzero_bitwise)]
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let n = NonZero::new(", $rot_op, stringify!($Int), ")?;")]
            #[doc = concat!("let m = NonZero::new(", $rot_result, ")?;")]
            ///
            #[doc = concat!("assert_eq!(n.rotate_left(", $rot, "), m);")]
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "nonzero_bitwise", issue = "128281")]
            #[must_use = "this returns the result of the operation, \
                        without modifying the original"]
            #[inline(always)]
            #[ensures(|result| result.get() != 0)]
            #[ensures(|result| result.rotate_right(n).get() == old(self).get())]
            pub const fn rotate_left(self, n: u32) -> Self {
                let result = self.get().rotate_left(n);
                // SAFETY: Rotating bits preserves the property int > 0.
                unsafe { Self::new_unchecked(result) }
            }

            /// Shifts the bits to the right by a specified amount, `n`,
            /// wrapping the truncated bits to the beginning of the resulting
            /// integer.
            ///
            /// Please note this isn't the same operation as the `>>` shifting operator!
            ///
            /// # Examples
            ///
            /// ```
            /// #![feature(nonzero_bitwise)]
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let n = NonZero::new(", $rot_result, stringify!($Int), ")?;")]
            #[doc = concat!("let m = NonZero::new(", $rot_op, ")?;")]
            ///
            #[doc = concat!("assert_eq!(n.rotate_right(", $rot, "), m);")]
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "nonzero_bitwise", issue = "128281")]
            #[must_use = "this returns the result of the operation, \
                        without modifying the original"]
            #[inline(always)]
            #[ensures(|result| result.get() != 0)]
            #[ensures(|result| result.rotate_left(n).get() == old(self).get())]
            pub const fn rotate_right(self, n: u32) -> Self {
                let result = self.get().rotate_right(n);
                // SAFETY: Rotating bits preserves the property int > 0.
                unsafe { Self::new_unchecked(result) }
            }

            /// Reverses the byte order of the integer.
            ///
            /// # Examples
            ///
            /// ```
            /// #![feature(nonzero_bitwise)]
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let n = NonZero::new(", $swap_op, stringify!($Int), ")?;")]
            /// let m = n.swap_bytes();
            ///
            #[doc = concat!("assert_eq!(m, NonZero::new(", $swapped, ")?);")]
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "nonzero_bitwise", issue = "128281")]
            #[must_use = "this returns the result of the operation, \
                        without modifying the original"]
            #[inline(always)]
            #[ensures(|result| result.get() != 0)]
            #[ensures(|result| result.get() == old(self).get().swap_bytes())]
            pub const fn swap_bytes(self) -> Self {
                let result = self.get().swap_bytes();
                // SAFETY: Shuffling bytes preserves the property int > 0.
                unsafe { Self::new_unchecked(result) }
            }

            /// Reverses the order of bits in the integer. The least significant bit becomes the most significant bit,
            /// second least-significant bit becomes second most-significant bit, etc.
            ///
            /// # Examples
            ///
            /// ```
            /// #![feature(nonzero_bitwise)]
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let n = NonZero::new(", $swap_op, stringify!($Int), ")?;")]
            /// let m = n.reverse_bits();
            ///
            #[doc = concat!("assert_eq!(m, NonZero::new(", $reversed, ")?);")]
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "nonzero_bitwise", issue = "128281")]
            #[must_use = "this returns the result of the operation, \
                        without modifying the original"]
            #[inline(always)]
            #[ensures(|result| result.get() != 0)]
            #[ensures(|result| result.get() == old(self).get().reverse_bits())]
            pub const fn reverse_bits(self) -> Self {
                let result = self.get().reverse_bits();
                // SAFETY: Reversing bits preserves the property int > 0.
                unsafe { Self::new_unchecked(result) }
            }

            /// Converts an integer from big endian to the target's endianness.
            ///
            /// On big endian this is a no-op. On little endian the bytes are
            /// swapped.
            ///
            /// # Examples
            ///
            /// ```
            /// #![feature(nonzero_bitwise)]
            /// # use std::num::NonZero;
            #[doc = concat!("use std::num::", stringify!($Ty), ";")]
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let n = NonZero::new(0x1A", stringify!($Int), ")?;")]
            ///
            /// if cfg!(target_endian = "big") {
            #[doc = concat!("    assert_eq!(", stringify!($Ty), "::from_be(n), n)")]
            /// } else {
            #[doc = concat!("    assert_eq!(", stringify!($Ty), "::from_be(n), n.swap_bytes())")]
            /// }
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "nonzero_bitwise", issue = "128281")]
            #[must_use]
            #[inline(always)]
            #[ensures(|result| result.get() != 0)]
            #[ensures(|result| result.get() == $Int::from_be(x.get()))]
            pub const fn from_be(x: Self) -> Self {
                let result = $Int::from_be(x.get());
                // SAFETY: Shuffling bytes preserves the property int > 0.
                unsafe { Self::new_unchecked(result) }
            }

            /// Converts an integer from little endian to the target's endianness.
            ///
            /// On little endian this is a no-op. On big endian the bytes are
            /// swapped.
            ///
            /// # Examples
            ///
            /// ```
            /// #![feature(nonzero_bitwise)]
            /// # use std::num::NonZero;
            #[doc = concat!("use std::num::", stringify!($Ty), ";")]
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let n = NonZero::new(0x1A", stringify!($Int), ")?;")]
            ///
            /// if cfg!(target_endian = "little") {
            #[doc = concat!("    assert_eq!(", stringify!($Ty), "::from_le(n), n)")]
            /// } else {
            #[doc = concat!("    assert_eq!(", stringify!($Ty), "::from_le(n), n.swap_bytes())")]
            /// }
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "nonzero_bitwise", issue = "128281")]
            #[must_use]
            #[inline(always)]
            #[ensures(|result| result.get() != 0)]
            #[ensures(|result| result.get() == $Int::from_le(x.get()))]
            pub const fn from_le(x: Self) -> Self {
                let result = $Int::from_le(x.get());
                // SAFETY: Shuffling bytes preserves the property int > 0.
                unsafe { Self::new_unchecked(result) }
            }

            /// Converts `self` to big endian from the target's endianness.
            ///
            /// On big endian this is a no-op. On little endian the bytes are
            /// swapped.
            ///
            /// # Examples
            ///
            /// ```
            /// #![feature(nonzero_bitwise)]
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let n = NonZero::new(0x1A", stringify!($Int), ")?;")]
            ///
            /// if cfg!(target_endian = "big") {
            ///     assert_eq!(n.to_be(), n)
            /// } else {
            ///     assert_eq!(n.to_be(), n.swap_bytes())
            /// }
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "nonzero_bitwise", issue = "128281")]
            #[must_use = "this returns the result of the operation, \
                        without modifying the original"]
            #[inline(always)]
            #[ensures(|result| result.get() != 0)]
            #[ensures(|result| result.get() == old(self).get().to_be())]
            pub const fn to_be(self) -> Self {
                let result = self.get().to_be();
                // SAFETY: Shuffling bytes preserves the property int > 0.
                unsafe { Self::new_unchecked(result) }
            }

            /// Converts `self` to little endian from the target's endianness.
            ///
            /// On little endian this is a no-op. On big endian the bytes are
            /// swapped.
            ///
            /// # Examples
            ///
            /// ```
            /// #![feature(nonzero_bitwise)]
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let n = NonZero::new(0x1A", stringify!($Int), ")?;")]
            ///
            /// if cfg!(target_endian = "little") {
            ///     assert_eq!(n.to_le(), n)
            /// } else {
            ///     assert_eq!(n.to_le(), n.swap_bytes())
            /// }
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "nonzero_bitwise", issue = "128281")]
            #[must_use = "this returns the result of the operation, \
                        without modifying the original"]
            #[inline(always)]
            #[ensures(|result| result.get() != 0)]
            #[ensures(|result| result.get() == old(self).get().to_le())]
            pub const fn to_le(self) -> Self {
                let result = self.get().to_le();
                // SAFETY: Shuffling bytes preserves the property int > 0.
                unsafe { Self::new_unchecked(result) }
            }

            nonzero_integer_signedness_dependent_methods! {
                Primitive = $signedness $Int,
                SignedPrimitive = $Sint,
                UnsignedPrimitive = $Uint,
            }

            /// Multiplies two non-zero integers together.
            /// Checks for overflow and returns [`None`] on overflow.
            /// As a consequence, the result cannot wrap to zero.
            ///
            /// # Examples
            ///
            /// ```
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let two = NonZero::new(2", stringify!($Int), ")?;")]
            #[doc = concat!("let four = NonZero::new(4", stringify!($Int), ")?;")]
            #[doc = concat!("let max = NonZero::new(", stringify!($Int), "::MAX)?;")]
            ///
            /// assert_eq!(Some(four), two.checked_mul(two));
            /// assert_eq!(None, max.checked_mul(two));
            /// # Some(())
            /// # }
            /// ```
            #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
            #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
            #[must_use = "this returns the result of the operation, \
                          without modifying the original"]
            #[inline]
            #[ensures(|result: &Option<Self>| {
                // `Some` iff no overflow, with the exact product — which is
                // nonzero (nonzero factors), discharging `new_unchecked`.
                match result {
                    Some(v) => self.get().checked_mul(other.get()) == Some(v.get()),
                    None => self.get().checked_mul(other.get()).is_none(),
                }
            })]
            pub const fn checked_mul(self, other: Self) -> Option<Self> {
                if let Some(result) = self.get().checked_mul(other.get()) {
                    // SAFETY:
                    // - `checked_mul` returns `None` on overflow
                    // - `self` and `other` are non-zero
                    // - the only way to get zero from a multiplication without overflow is for one
                    //   of the sides to be zero
                    //
                    // So the result cannot be zero.
                    Some(unsafe { Self::new_unchecked(result) })
                } else {
                    None
                }
            }

            /// Multiplies two non-zero integers together.
            #[doc = concat!("Return [`NonZero::<", stringify!($Int), ">::MAX`] on overflow.")]
            ///
            /// # Examples
            ///
            /// ```
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let two = NonZero::new(2", stringify!($Int), ")?;")]
            #[doc = concat!("let four = NonZero::new(4", stringify!($Int), ")?;")]
            #[doc = concat!("let max = NonZero::new(", stringify!($Int), "::MAX)?;")]
            ///
            /// assert_eq!(four, two.saturating_mul(two));
            /// assert_eq!(max, four.saturating_mul(max));
            /// # Some(())
            /// # }
            /// ```
            #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
            #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
            #[must_use = "this returns the result of the operation, \
                          without modifying the original"]
            #[inline]
            #[ensures(|result: &Self| {
                // Exact `saturating_mul` value — nonzero both when the product
                // fits (nonzero factors) and when it saturates (`MAX`/`MIN`),
                // discharging `new_unchecked`.
                result.get() == self.get().saturating_mul(other.get())
            })]
            pub const fn saturating_mul(self, other: Self) -> Self {
                // SAFETY:
                // - `saturating_mul` returns `u*::MAX`/`i*::MAX`/`i*::MIN` on overflow/underflow,
                //   all of which are non-zero
                // - `self` and `other` are non-zero
                // - the only way to get zero from a multiplication without overflow is for one
                //   of the sides to be zero
                //
                // So the result cannot be zero.
                unsafe { Self::new_unchecked(self.get().saturating_mul(other.get())) }
            }

            /// Multiplies two non-zero integers together,
            /// assuming overflow cannot occur.
            /// Overflow is unchecked, and it is undefined behavior to overflow
            /// *even if the result would wrap to a non-zero value*.
            /// The behavior is undefined as soon as
            #[doc = sign_dependent_expr!{
                $signedness ?
                if signed {
                    concat!("`self * rhs > ", stringify!($Int), "::MAX`, ",
                            "or `self * rhs < ", stringify!($Int), "::MIN`.")
                }
                if unsigned {
                    concat!("`self * rhs > ", stringify!($Int), "::MAX`.")
                }
            }]
            ///
            /// # Examples
            ///
            /// ```
            /// #![feature(nonzero_ops)]
            ///
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let two = NonZero::new(2", stringify!($Int), ")?;")]
            #[doc = concat!("let four = NonZero::new(4", stringify!($Int), ")?;")]
            ///
            /// assert_eq!(four, unsafe { two.unchecked_mul(two) });
            /// # Some(())
            /// # }
            /// ```
            #[unstable(feature = "nonzero_ops", issue = "84186")]
            #[must_use = "this returns the result of the operation, \
                          without modifying the original"]
            #[inline]
            #[requires({
                self.get().checked_mul(other.get()).is_some()
            })]
            #[ensures(|result: &Self| {
                self.get().checked_mul(other.get()).is_some_and(|product| product == result.get())
            })]
            pub const unsafe fn unchecked_mul(self, other: Self) -> Self {
                // SAFETY: The caller ensures there is no overflow.
                unsafe { Self::new_unchecked(self.get().unchecked_mul(other.get())) }
            }

            /// Raises non-zero value to an integer power.
            /// Checks for overflow and returns [`None`] on overflow.
            /// As a consequence, the result cannot wrap to zero.
            ///
            /// # Examples
            ///
            /// ```
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let three = NonZero::new(3", stringify!($Int), ")?;")]
            #[doc = concat!("let twenty_seven = NonZero::new(27", stringify!($Int), ")?;")]
            #[doc = concat!("let half_max = NonZero::new(", stringify!($Int), "::MAX / 2)?;")]
            ///
            /// assert_eq!(Some(twenty_seven), three.checked_pow(3));
            /// assert_eq!(None, half_max.checked_pow(3));
            /// # Some(())
            /// # }
            /// ```
            #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
            #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
            #[must_use = "this returns the result of the operation, \
                          without modifying the original"]
            #[inline]
            #[ensures(|result: &Option<Self>| {
                // Safety property, verified unboundedly: a non-overflowing
                // power of a nonzero base is nonzero, discharging
                // `new_unchecked`. No exact-value clause: under
                // `-Z loop-contracts` the pow loop is abstracted by its
                // `safety::loop_invariant`, and only invariant-derived facts
                // (nonzero-ness) survive — a functional invariant would need
                // ghost state for the original exponent.
                match result {
                    Some(v) => v.get() != 0,
                    None => true,
                }
            })]
            pub const fn checked_pow(self, other: u32) -> Option<Self> {
                if let Some(result) = self.get().checked_pow(other) {
                    // SAFETY:
                    // - `checked_pow` returns `None` on overflow/underflow
                    // - `self` is non-zero
                    // - the only way to get zero from an exponentiation without overflow is
                    //   for base to be zero
                    //
                    // So the result cannot be zero.
                    Some(unsafe { Self::new_unchecked(result) })
                } else {
                    None
                }
            }

            /// Raise non-zero value to an integer power.
            #[doc = sign_dependent_expr!{
                $signedness ?
                if signed {
                    concat!("Return [`NonZero::<", stringify!($Int), ">::MIN`] ",
                                "or [`NonZero::<", stringify!($Int), ">::MAX`] on overflow.")
                }
                if unsigned {
                    concat!("Return [`NonZero::<", stringify!($Int), ">::MAX`] on overflow.")
                }
            }]
            ///
            /// # Examples
            ///
            /// ```
            /// # use std::num::NonZero;
            /// #
            /// # fn main() { test().unwrap(); }
            /// # fn test() -> Option<()> {
            #[doc = concat!("let three = NonZero::new(3", stringify!($Int), ")?;")]
            #[doc = concat!("let twenty_seven = NonZero::new(27", stringify!($Int), ")?;")]
            #[doc = concat!("let max = NonZero::new(", stringify!($Int), "::MAX)?;")]
            ///
            /// assert_eq!(twenty_seven, three.saturating_pow(3));
            /// assert_eq!(max, max.saturating_pow(3));
            /// # Some(())
            /// # }
            /// ```
            #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
            #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
            #[must_use = "this returns the result of the operation, \
                          without modifying the original"]
            #[inline]
            #[ensures(|result: &Self| {
                // Safety property, verified unboundedly: nonzero both in-range
                // (nonzero factors) and when saturating (`MAX`/`MIN`),
                // discharging `new_unchecked`. No exact-value clause — same
                // loop-abstraction trade-off as `checked_pow` above.
                result.get() != 0
            })]
            pub const fn saturating_pow(self, other: u32) -> Self {
                // SAFETY:
                // - `saturating_pow` returns `u*::MAX`/`i*::MAX`/`i*::MIN` on overflow/underflow,
                //   all of which are non-zero
                // - `self` is non-zero
                // - the only way to get zero from an exponentiation without overflow is
                //   for base to be zero
                //
                // So the result cannot be zero.
                unsafe { Self::new_unchecked(self.get().saturating_pow(other)) }
            }
        }

        #[stable(feature = "nonzero_parse", since = "1.35.0")]
        impl FromStr for NonZero<$Int> {
            type Err = ParseIntError;
            fn from_str(src: &str) -> Result<Self, Self::Err> {
                Self::new(<$Int>::from_str_radix(src, 10)?)
                    .ok_or(ParseIntError {
                        kind: IntErrorKind::Zero
                    })
            }
        }

        nonzero_integer_signedness_dependent_impls!($signedness $Int);
    };

    (
        Self = $Ty:ident,
        Primitive = unsigned $Int:ident,
        SignedPrimitive = $Sint:ident,
        rot = $rot:literal,
        rot_op = $rot_op:literal,
        rot_result = $rot_result:literal,
        swap_op = $swap_op:literal,
        swapped = $swapped:literal,
        reversed = $reversed:literal,
        $(,)?
    ) => {
        nonzero_integer! {
            #[stable(feature = "nonzero", since = "1.28.0")]
            Self = $Ty,
            Primitive = unsigned $Int,
            SignedPrimitive = $Sint,
            UnsignedPrimitive = $Int,
            rot = $rot,
            rot_op = $rot_op,
            rot_result = $rot_result,
            swap_op = $swap_op,
            swapped = $swapped,
            reversed = $reversed,
            leading_zeros_test = concat!(stringify!($Int), "::MAX"),
        }
    };

    (
        Self = $Ty:ident,
        Primitive = signed $Int:ident,
        UnsignedPrimitive = $Uint:ident,
        rot = $rot:literal,
        rot_op = $rot_op:literal,
        rot_result = $rot_result:literal,
        swap_op = $swap_op:literal,
        swapped = $swapped:literal,
        reversed = $reversed:literal,
    ) => {
        nonzero_integer! {
            #[stable(feature = "signed_nonzero", since = "1.34.0")]
            Self = $Ty,
            Primitive = signed $Int,
            SignedPrimitive = $Int,
            UnsignedPrimitive = $Uint,
            rot = $rot,
            rot_op = $rot_op,
            rot_result = $rot_result,
            swap_op = $swap_op,
            swapped = $swapped,
            reversed = $reversed,
            leading_zeros_test = concat!("-1", stringify!($Int)),
        }
    };
}

macro_rules! nonzero_integer_signedness_dependent_impls {
    // Impls for unsigned nonzero types only.
    (unsigned $Int:ty) => {
        #[stable(feature = "nonzero_div", since = "1.51.0")]
        #[rustc_const_unstable(feature = "const_ops", issue = "143802")]
        impl const Div<NonZero<$Int>> for $Int {
            type Output = $Int;

            /// Same as `self / other.get()`, but because `other` is a `NonZero<_>`,
            /// there's never a runtime check for division-by-zero.
            ///
            /// This operation rounds towards zero, truncating any fractional
            /// part of the exact result, and cannot panic.
            #[doc(alias = "unchecked_div")]
            #[inline]
            fn div(self, other: NonZero<$Int>) -> $Int {
                // SAFETY: Division by zero is checked because `other` is non-zero,
                // and MIN/-1 is checked because `self` is an unsigned int.
                unsafe { intrinsics::unchecked_div(self, other.get()) }
            }
        }

        #[stable(feature = "nonzero_div_assign", since = "1.79.0")]
        #[rustc_const_unstable(feature = "const_ops", issue = "143802")]
        impl const DivAssign<NonZero<$Int>> for $Int {
            /// Same as `self /= other.get()`, but because `other` is a `NonZero<_>`,
            /// there's never a runtime check for division-by-zero.
            ///
            /// This operation rounds towards zero, truncating any fractional
            /// part of the exact result, and cannot panic.
            #[inline]
            fn div_assign(&mut self, other: NonZero<$Int>) {
                *self = *self / other;
            }
        }

        #[stable(feature = "nonzero_div", since = "1.51.0")]
        #[rustc_const_unstable(feature = "const_ops", issue = "143802")]
        impl const Rem<NonZero<$Int>> for $Int {
            type Output = $Int;

            /// This operation satisfies `n % d == n - (n / d) * d`, and cannot panic.
            #[inline]
            fn rem(self, other: NonZero<$Int>) -> $Int {
                // SAFETY: Remainder by zero is checked because `other` is non-zero,
                // and MIN/-1 is checked because `self` is an unsigned int.
                unsafe { intrinsics::unchecked_rem(self, other.get()) }
            }
        }

        #[stable(feature = "nonzero_div_assign", since = "1.79.0")]
        #[rustc_const_unstable(feature = "const_ops", issue = "143802")]
        impl const RemAssign<NonZero<$Int>> for $Int {
            /// This operation satisfies `n % d == n - (n / d) * d`, and cannot panic.
            #[inline]
            fn rem_assign(&mut self, other: NonZero<$Int>) {
                *self = *self % other;
            }
        }

        impl NonZero<$Int> {
            /// Calculates the quotient of `self` and `rhs`, rounding the result towards positive infinity.
            ///
            /// The result is guaranteed to be non-zero.
            ///
            /// # Examples
            ///
            /// ```
            /// # use std::num::NonZero;
            #[doc = concat!("let one = NonZero::new(1", stringify!($Int), ").unwrap();")]
            #[doc = concat!("let max = NonZero::new(", stringify!($Int), "::MAX).unwrap();")]
            /// assert_eq!(one.div_ceil(max), one);
            ///
            #[doc = concat!("let two = NonZero::new(2", stringify!($Int), ").unwrap();")]
            #[doc = concat!("let three = NonZero::new(3", stringify!($Int), ").unwrap();")]
            /// assert_eq!(three.div_ceil(two), two);
            /// ```
            #[stable(feature = "unsigned_nonzero_div_ceil", since = "1.92.0")]
            #[rustc_const_stable(feature = "unsigned_nonzero_div_ceil", since = "1.92.0")]
            #[must_use = "this returns the result of the operation, \
                          without modifying the original"]
            #[inline]
            pub const fn div_ceil(self, rhs: Self) -> Self {
                let v = self.get().div_ceil(rhs.get());
                // SAFETY: ceiled division of two positive integers can never be zero.
                unsafe { Self::new_unchecked(v) }
            }
        }
    };
    // Impls for signed nonzero types only.
    (signed $Int:ty) => {
        #[stable(feature = "signed_nonzero_neg", since = "1.71.0")]
        #[rustc_const_unstable(feature = "const_ops", issue = "143802")]
        impl const Neg for NonZero<$Int> {
            type Output = Self;

            #[inline]
            fn neg(self) -> Self {
                // SAFETY: negation of nonzero cannot yield zero values.
                unsafe { Self::new_unchecked(self.get().neg()) }
            }
        }

        forward_ref_unop! { impl Neg, neg for NonZero<$Int>,
        #[stable(feature = "signed_nonzero_neg", since = "1.71.0")]
        #[rustc_const_unstable(feature = "const_ops", issue = "143802")] }
    };
}

#[rustfmt::skip] // https://github.com/rust-lang/rustfmt/issues/5974
macro_rules! nonzero_integer_signedness_dependent_methods {
    // Associated items for unsigned nonzero types only.
    (
        Primitive = unsigned $Int:ident,
        SignedPrimitive = $Sint:ty,
        UnsignedPrimitive = $Uint:ty,
    ) => {
        /// The smallest value that can be represented by this non-zero
        /// integer type, 1.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::MIN.get(), 1", stringify!($Int), ");")]
        /// ```
        #[stable(feature = "nonzero_min_max", since = "1.70.0")]
        pub const MIN: Self = Self::new(1).unwrap();

        /// The largest value that can be represented by this non-zero
        /// integer type,
        #[doc = concat!("equal to [`", stringify!($Int), "::MAX`].")]
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::MAX.get(), ", stringify!($Int), "::MAX);")]
        /// ```
        #[stable(feature = "nonzero_min_max", since = "1.70.0")]
        pub const MAX: Self = Self::new(<$Int>::MAX).unwrap();

        /// Adds an unsigned integer to a non-zero value.
        /// Checks for overflow and returns [`None`] on overflow.
        /// As a consequence, the result cannot wrap to zero.
        ///
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let one = NonZero::new(1", stringify!($Int), ")?;")]
        #[doc = concat!("let two = NonZero::new(2", stringify!($Int), ")?;")]
        #[doc = concat!("let max = NonZero::new(", stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(Some(two), one.checked_add(1));
        /// assert_eq!(None, max.checked_add(1));
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
        #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        #[ensures(|result: &Option<Self>| {
            // `Some` iff no overflow, with the exact sum — which is >= 1
            // (nonzero + unsigned), discharging `new_unchecked`.
            match result {
                Some(v) => self.get().checked_add(other) == Some(v.get()),
                None => self.get().checked_add(other).is_none(),
            }
        })]
        pub const fn checked_add(self, other: $Int) -> Option<Self> {
            if let Some(result) = self.get().checked_add(other) {
                // SAFETY:
                // - `checked_add` returns `None` on overflow
                // - `self` is non-zero
                // - the only way to get zero from an addition without overflow is for both
                //   sides to be zero
                //
                // So the result cannot be zero.
                Some(unsafe { Self::new_unchecked(result) })
            } else {
                None
            }
        }

        /// Adds an unsigned integer to a non-zero value.
        #[doc = concat!("Return [`NonZero::<", stringify!($Int), ">::MAX`] on overflow.")]
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let one = NonZero::new(1", stringify!($Int), ")?;")]
        #[doc = concat!("let two = NonZero::new(2", stringify!($Int), ")?;")]
        #[doc = concat!("let max = NonZero::new(", stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(two, one.saturating_add(1));
        /// assert_eq!(max, max.saturating_add(1));
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
        #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        #[ensures(|result: &Self| {
            // Exact `saturating_add` value — >= 1 both when the sum fits
            // (nonzero + unsigned) and on overflow (`MAX`), discharging
            // `new_unchecked`.
            result.get() == self.get().saturating_add(other)
        })]
        pub const fn saturating_add(self, other: $Int) -> Self {
            // SAFETY:
            // - `saturating_add` returns `u*::MAX` on overflow, which is non-zero
            // - `self` is non-zero
            // - the only way to get zero from an addition without overflow is for both
            //   sides to be zero
            //
            // So the result cannot be zero.
            unsafe { Self::new_unchecked(self.get().saturating_add(other)) }
        }

        /// Adds an unsigned integer to a non-zero value,
        /// assuming overflow cannot occur.
        /// Overflow is unchecked, and it is undefined behavior to overflow
        /// *even if the result would wrap to a non-zero value*.
        /// The behavior is undefined as soon as
        #[doc = concat!("`self + rhs > ", stringify!($Int), "::MAX`.")]
        ///
        /// # Examples
        ///
        /// ```
        /// #![feature(nonzero_ops)]
        ///
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let one = NonZero::new(1", stringify!($Int), ")?;")]
        #[doc = concat!("let two = NonZero::new(2", stringify!($Int), ")?;")]
        ///
        /// assert_eq!(two, unsafe { one.unchecked_add(1) });
        /// # Some(())
        /// # }
        /// ```
        #[unstable(feature = "nonzero_ops", issue = "84186")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        #[requires({
            self.get().checked_add(other).is_some()
        })]
        #[ensures(|result: &Self| {
            // Postcondition: the result matches the expected addition
            self.get().checked_add(other).is_some_and(|sum| sum == result.get())
        })]
        pub const unsafe fn unchecked_add(self, other: $Int) -> Self {
            // SAFETY: The caller ensures there is no overflow.
            unsafe { Self::new_unchecked(self.get().unchecked_add(other)) }
        }

        /// Returns the smallest power of two greater than or equal to `self`.
        /// Checks for overflow and returns [`None`]
        /// if the next power of two is greater than the type’s maximum value.
        /// As a consequence, the result cannot wrap to zero.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let two = NonZero::new(2", stringify!($Int), ")?;")]
        #[doc = concat!("let three = NonZero::new(3", stringify!($Int), ")?;")]
        #[doc = concat!("let four = NonZero::new(4", stringify!($Int), ")?;")]
        #[doc = concat!("let max = NonZero::new(", stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(Some(two), two.checked_next_power_of_two() );
        /// assert_eq!(Some(four), three.checked_next_power_of_two() );
        /// assert_eq!(None, max.checked_next_power_of_two() );
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
        #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        #[ensures(|result: &Option<Self>| {
            // `Some` iff the next power of two fits, with the exact value —
            // which is >= 1 for input >= 1, discharging `new_unchecked`.
            match result {
                Some(v) => self.get().checked_next_power_of_two() == Some(v.get()),
                None => self.get().checked_next_power_of_two().is_none(),
            }
        })]
        pub const fn checked_next_power_of_two(self) -> Option<Self> {
            if let Some(nz) = self.get().checked_next_power_of_two() {
                // SAFETY: The next power of two is positive
                // and overflow is checked.
                Some(unsafe { Self::new_unchecked(nz) })
            } else {
                None
            }
        }

        /// Returns the base 2 logarithm of the number, rounded down.
        ///
        /// This is the same operation as
        #[doc = concat!("[`", stringify!($Int), "::ilog2`],")]
        /// except that it has no failure cases to worry about
        /// since this value can never be zero.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("assert_eq!(NonZero::new(7", stringify!($Int), ")?.ilog2(), 2);")]
        #[doc = concat!("assert_eq!(NonZero::new(8", stringify!($Int), ")?.ilog2(), 3);")]
        #[doc = concat!("assert_eq!(NonZero::new(9", stringify!($Int), ")?.ilog2(), 3);")]
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "int_log", since = "1.67.0")]
        #[rustc_const_stable(feature = "int_log", since = "1.67.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn ilog2(self) -> u32 {
            Self::BITS - 1 - self.leading_zeros()
        }

        /// Returns the base 10 logarithm of the number, rounded down.
        ///
        /// This is the same operation as
        #[doc = concat!("[`", stringify!($Int), "::ilog10`],")]
        /// except that it has no failure cases to worry about
        /// since this value can never be zero.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("assert_eq!(NonZero::new(99", stringify!($Int), ")?.ilog10(), 1);")]
        #[doc = concat!("assert_eq!(NonZero::new(100", stringify!($Int), ")?.ilog10(), 2);")]
        #[doc = concat!("assert_eq!(NonZero::new(101", stringify!($Int), ")?.ilog10(), 2);")]
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "int_log", since = "1.67.0")]
        #[rustc_const_stable(feature = "int_log", since = "1.67.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn ilog10(self) -> u32 {
            super::int_log10::$Int(self)
        }

        /// Calculates the midpoint (average) between `self` and `rhs`.
        ///
        /// `midpoint(a, b)` is `(a + b) >> 1` as if it were performed in a
        /// sufficiently-large signed integral type. This implies that the result is
        /// always rounded towards negative infinity and that no overflow will ever occur.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let one = NonZero::new(1", stringify!($Int), ")?;")]
        #[doc = concat!("let two = NonZero::new(2", stringify!($Int), ")?;")]
        #[doc = concat!("let four = NonZero::new(4", stringify!($Int), ")?;")]
        ///
        /// assert_eq!(one.midpoint(four), two);
        /// assert_eq!(four.midpoint(one), two);
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "num_midpoint", since = "1.85.0")]
        #[rustc_const_stable(feature = "num_midpoint", since = "1.85.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[doc(alias = "average_floor")]
        #[doc(alias = "average")]
        #[inline]
        #[ensures(|result: &Self| result.get() != 0)]
        #[ensures(|result: &Self| {
            // Exact overflow-free `midpoint` value — the average of two values
            // >= 1 is >= 1, discharging `new_unchecked`.
            result.get() == self.get().midpoint(rhs.get())
        })]
        pub const fn midpoint(self, rhs: Self) -> Self {
            // SAFETY: The only way to get `0` with midpoint is to have two opposite or
            // near opposite numbers: (-5, 5), (0, 1), (0, 0) which is impossible because
            // of the unsignedness of this number and also because `Self` is guaranteed to
            // never being 0.
            unsafe { Self::new_unchecked(self.get().midpoint(rhs.get())) }
        }

        /// Returns `true` if and only if `self == (1 << k)` for some `k`.
        ///
        /// On many architectures, this function can perform better than `is_power_of_two()`
        /// on the underlying integer type, as special handling of zero can be avoided.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let eight = NonZero::new(8", stringify!($Int), ")?;")]
        /// assert!(eight.is_power_of_two());
        #[doc = concat!("let ten = NonZero::new(10", stringify!($Int), ")?;")]
        /// assert!(!ten.is_power_of_two());
        /// # Some(())
        /// # }
        /// ```
        #[must_use]
        #[stable(feature = "nonzero_is_power_of_two", since = "1.59.0")]
        #[rustc_const_stable(feature = "nonzero_is_power_of_two", since = "1.59.0")]
        #[inline]
        pub const fn is_power_of_two(self) -> bool {
            // LLVM 11 normalizes `unchecked_sub(x, 1) & x == 0` to the implementation seen here.
            // On the basic x86-64 target, this saves 3 instructions for the zero check.
            // On x86_64 with BMI1, being nonzero lets it codegen to `BLSR`, which saves an instruction
            // compared to the `POPCNT` implementation on the underlying integer type.

            intrinsics::ctpop(self.get()) < 2
        }

        /// Returns the square root of the number, rounded down.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let ten = NonZero::new(10", stringify!($Int), ")?;")]
        #[doc = concat!("let three = NonZero::new(3", stringify!($Int), ")?;")]
        ///
        /// assert_eq!(ten.isqrt(), three);
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "isqrt", since = "1.84.0")]
        #[rustc_const_stable(feature = "isqrt", since = "1.84.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        #[ensures(|result: &Self| result.get() != 0)]
        #[ensures(|result: &Self| {
            // Exact `isqrt` value — `isqrt` is nondecreasing and the input is
            // >= 1, so the root is >= 1, discharging `new_unchecked`.
            result.get() == self.get().isqrt()
        })]
        pub const fn isqrt(self) -> Self {
            let result = self.get().isqrt();

            // SAFETY: Integer square root is a monotonically nondecreasing
            // function, which means that increasing the input will never cause
            // the output to decrease. Thus, since the input for nonzero
            // unsigned integers has a lower bound of 1, the lower bound of the
            // results will be sqrt(1), which is 1, so a result can't be zero.
            unsafe { Self::new_unchecked(result) }
        }

        /// Returns the bit pattern of `self` reinterpreted as a signed integer of the same size.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        ///
        #[doc = concat!("let n = NonZero::<", stringify!($Int), ">::MAX;")]
        ///
        #[doc = concat!("assert_eq!(n.cast_signed(), NonZero::new(-1", stringify!($Sint), ").unwrap());")]
        /// ```
        #[stable(feature = "integer_sign_cast", since = "1.87.0")]
        #[rustc_const_stable(feature = "integer_sign_cast", since = "1.87.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn cast_signed(self) -> NonZero<$Sint> {
            // SAFETY: `self.get()` can't be zero
            unsafe { NonZero::new_unchecked(self.get().cast_signed()) }
        }

        /// Returns the minimum number of bits required to represent `self`.
        ///
        /// # Examples
        ///
        /// ```
        /// #![feature(uint_bit_width)]
        ///
        /// # use core::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::MIN.bit_width(), NonZero::new(1)?);")]
        #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::new(0b111)?.bit_width(), NonZero::new(3)?);")]
        #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::new(0b1110)?.bit_width(), NonZero::new(4)?);")]
        /// # Some(())
        /// # }
        /// ```
        #[unstable(feature = "uint_bit_width", issue = "142326")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn bit_width(self) -> NonZero<u32> {
            // SAFETY: Since `self.leading_zeros()` is always less than
            // `Self::BITS`, this subtraction can never be zero.
            unsafe { NonZero::new_unchecked(Self::BITS - self.leading_zeros()) }
        }
    };

    // Associated items for signed nonzero types only.
    (
        Primitive = signed $Int:ident,
        SignedPrimitive = $Sint:ty,
        UnsignedPrimitive = $Uint:ty,
    ) => {
        /// The smallest value that can be represented by this non-zero
        /// integer type,
        #[doc = concat!("equal to [`", stringify!($Int), "::MIN`].")]
        ///
        /// Note: While most integer types are defined for every whole
        /// number between `MIN` and `MAX`, signed non-zero integers are
        /// a special case. They have a "gap" at 0.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::MIN.get(), ", stringify!($Int), "::MIN);")]
        /// ```
        #[stable(feature = "nonzero_min_max", since = "1.70.0")]
        pub const MIN: Self = Self::new(<$Int>::MIN).unwrap();

        /// The largest value that can be represented by this non-zero
        /// integer type,
        #[doc = concat!("equal to [`", stringify!($Int), "::MAX`].")]
        ///
        /// Note: While most integer types are defined for every whole
        /// number between `MIN` and `MAX`, signed non-zero integers are
        /// a special case. They have a "gap" at 0.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        #[doc = concat!("assert_eq!(NonZero::<", stringify!($Int), ">::MAX.get(), ", stringify!($Int), "::MAX);")]
        /// ```
        #[stable(feature = "nonzero_min_max", since = "1.70.0")]
        pub const MAX: Self = Self::new(<$Int>::MAX).unwrap();

        /// Computes the absolute value of self.
        #[doc = concat!("See [`", stringify!($Int), "::abs`]")]
        /// for documentation on overflow behavior.
        ///
        /// # Example
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos = NonZero::new(1", stringify!($Int), ")?;")]
        #[doc = concat!("let neg = NonZero::new(-1", stringify!($Int), ")?;")]
        ///
        /// assert_eq!(pos, pos.abs());
        /// assert_eq!(pos, neg.abs());
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
        #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        // `abs` is safe and total: `MIN` is a defined input (panics under overflow
        // checks, wraps to `MIN` otherwise), so no `#[requires]`. Both clauses hold
        // on every normal return in either build mode. The result is deliberately
        // not claimed positive: with overflow checks off, `MIN` wraps to the
        // negative `MIN`. Nonzero-ness discharges the internal `new_unchecked`.
        // Signed `NonZero` only; see the paired value/panic harnesses.
        #[ensures(|result: &Self| result.get() != 0)]
        #[ensures(|result: &Self| result.get() == self.get().abs())]
        pub const fn abs(self) -> Self {
            // SAFETY: This cannot overflow to zero.
            unsafe { Self::new_unchecked(self.get().abs()) }
        }

        /// Checked absolute value.
        /// Checks for overflow and returns [`None`] if
        #[doc = concat!("`self == NonZero::<", stringify!($Int), ">::MIN`.")]
        /// The result cannot be zero.
        ///
        /// # Example
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos = NonZero::new(1", stringify!($Int), ")?;")]
        #[doc = concat!("let neg = NonZero::new(-1", stringify!($Int), ")?;")]
        #[doc = concat!("let min = NonZero::new(", stringify!($Int), "::MIN)?;")]
        ///
        /// assert_eq!(Some(pos), neg.checked_abs());
        /// assert_eq!(None, min.checked_abs());
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
        #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        // `None` exactly for `MIN` (the only overflowing input), else `Some(|self|)`;
        // `|x|` of nonzero is nonzero, discharging the internal `new_unchecked`.
        // `wrapping_abs` keeps the value clause itself overflow-free. Signed
        // `NonZero` only.
        #[ensures(|result: &Option<Self>| result.is_none() == (self.get() == <$Int>::MIN))]
        #[ensures(|result: &Option<Self>| result.is_none() || result.unwrap().get() == self.get().wrapping_abs())]
        pub const fn checked_abs(self) -> Option<Self> {
            if let Some(nz) = self.get().checked_abs() {
                // SAFETY: absolute value of nonzero cannot yield zero values.
                Some(unsafe { Self::new_unchecked(nz) })
            } else {
                None
            }
        }

        /// Computes the absolute value of self,
        /// with overflow information, see
        #[doc = concat!("[`", stringify!($Int), "::overflowing_abs`].")]
        ///
        /// # Example
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos = NonZero::new(1", stringify!($Int), ")?;")]
        #[doc = concat!("let neg = NonZero::new(-1", stringify!($Int), ")?;")]
        #[doc = concat!("let min = NonZero::new(", stringify!($Int), "::MIN)?;")]
        ///
        /// assert_eq!((pos, false), pos.overflowing_abs());
        /// assert_eq!((pos, false), neg.overflowing_abs());
        /// assert_eq!((min, true), min.overflowing_abs());
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
        #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        // The flag is exactly `self == MIN`; the value always equals
        // `self.wrapping_abs()`, which is nonzero for nonzero input, discharging the
        // internal `new_unchecked`. `wrapping_abs` keeps the value clause itself
        // overflow-free. Signed `NonZero` only.
        #[ensures(|result: &(Self, bool)| result.1 == (self.get() == <$Int>::MIN))]
        #[ensures(|result: &(Self, bool)| result.0.get() == self.get().wrapping_abs())]
        pub const fn overflowing_abs(self) -> (Self, bool) {
            let (nz, flag) = self.get().overflowing_abs();
            (
                // SAFETY: absolute value of nonzero cannot yield zero values.
                unsafe { Self::new_unchecked(nz) },
                flag,
            )
        }

        /// Saturating absolute value, see
        #[doc = concat!("[`", stringify!($Int), "::saturating_abs`].")]
        ///
        /// # Example
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos = NonZero::new(1", stringify!($Int), ")?;")]
        #[doc = concat!("let neg = NonZero::new(-1", stringify!($Int), ")?;")]
        #[doc = concat!("let min = NonZero::new(", stringify!($Int), "::MIN)?;")]
        #[doc = concat!("let min_plus = NonZero::new(", stringify!($Int), "::MIN + 1)?;")]
        #[doc = concat!("let max = NonZero::new(", stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(pos, pos.saturating_abs());
        /// assert_eq!(pos, neg.saturating_abs());
        /// assert_eq!(max, min.saturating_abs());
        /// assert_eq!(max, min_plus.saturating_abs());
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
        #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        // `|self|` with `MIN` clamped to `MAX`: strictly positive for nonzero input,
        // discharging the internal `new_unchecked`. The value clause is itself
        // overflow-free. Signed `NonZero` only.
        #[ensures(|result: &Self| result.get() > 0)]
        #[ensures(|result: &Self| result.get() == self.get().saturating_abs())]
        pub const fn saturating_abs(self) -> Self {
            // SAFETY: absolute value of nonzero cannot yield zero values.
            unsafe { Self::new_unchecked(self.get().saturating_abs()) }
        }

        /// Wrapping absolute value, see
        #[doc = concat!("[`", stringify!($Int), "::wrapping_abs`].")]
        ///
        /// # Example
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos = NonZero::new(1", stringify!($Int), ")?;")]
        #[doc = concat!("let neg = NonZero::new(-1", stringify!($Int), ")?;")]
        #[doc = concat!("let min = NonZero::new(", stringify!($Int), "::MIN)?;")]
        #[doc = concat!("# let max = NonZero::new(", stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(pos, pos.wrapping_abs());
        /// assert_eq!(pos, neg.wrapping_abs());
        /// assert_eq!(min, min.wrapping_abs());
        /// assert_eq!(max, (-max).wrapping_abs());
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
        #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        // `|self|` with `MIN` wrapping to `MIN`: never zero for nonzero input,
        // discharging the internal `new_unchecked`. Not claimed positive — `MIN`
        // wraps to the negative `MIN`. Signed `NonZero` only.
        #[ensures(|result: &Self| result.get() == self.get().wrapping_abs())]
        pub const fn wrapping_abs(self) -> Self {
            // SAFETY: absolute value of nonzero cannot yield zero values.
            unsafe { Self::new_unchecked(self.get().wrapping_abs()) }
        }

        /// Computes the absolute value of self
        /// without any wrapping or panicking.
        ///
        /// # Example
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let u_pos = NonZero::new(1", stringify!($Uint), ")?;")]
        #[doc = concat!("let i_pos = NonZero::new(1", stringify!($Int), ")?;")]
        #[doc = concat!("let i_neg = NonZero::new(-1", stringify!($Int), ")?;")]
        #[doc = concat!("let i_min = NonZero::new(", stringify!($Int), "::MIN)?;")]
        #[doc = concat!("let u_max = NonZero::new(", stringify!($Uint), "::MAX / 2 + 1)?;")]
        ///
        /// assert_eq!(u_pos, i_pos.unsigned_abs());
        /// assert_eq!(u_pos, i_neg.unsigned_abs());
        /// assert_eq!(u_max, i_min.unsigned_abs());
        /// # Some(())
        /// # }
        /// ```
        #[stable(feature = "nonzero_checked_ops", since = "1.64.0")]
        #[rustc_const_stable(feature = "const_nonzero_checked_ops", since = "1.64.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        // The magnitude of every signed value fits the unsigned width (`MIN` maps to
        // `2^(N-1)`), so the value clause is overflow-free and the result strictly
        // positive, discharging the internal `new_unchecked`. Signed `NonZero` only;
        // returns the corresponding unsigned `NonZero`.
        #[ensures(|result: &NonZero<$Uint>| result.get() > 0)]
        #[ensures(|result: &NonZero<$Uint>| result.get() == self.get().unsigned_abs())]
        pub const fn unsigned_abs(self) -> NonZero<$Uint> {
            // SAFETY: absolute value of nonzero cannot yield zero values.
            unsafe { NonZero::new_unchecked(self.get().unsigned_abs()) }
        }

        /// Returns `true` if `self` is positive and `false` if the
        /// number is negative.
        ///
        /// # Example
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos_five = NonZero::new(5", stringify!($Int), ")?;")]
        #[doc = concat!("let neg_five = NonZero::new(-5", stringify!($Int), ")?;")]
        ///
        /// assert!(pos_five.is_positive());
        /// assert!(!neg_five.is_positive());
        /// # Some(())
        /// # }
        /// ```
        #[must_use]
        #[inline]
        #[stable(feature = "nonzero_negation_ops", since = "1.71.0")]
        #[rustc_const_stable(feature = "nonzero_negation_ops", since = "1.71.0")]
        pub const fn is_positive(self) -> bool {
            self.get().is_positive()
        }

        /// Returns `true` if `self` is negative and `false` if the
        /// number is positive.
        ///
        /// # Example
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos_five = NonZero::new(5", stringify!($Int), ")?;")]
        #[doc = concat!("let neg_five = NonZero::new(-5", stringify!($Int), ")?;")]
        ///
        /// assert!(neg_five.is_negative());
        /// assert!(!pos_five.is_negative());
        /// # Some(())
        /// # }
        /// ```
        #[must_use]
        #[inline]
        #[stable(feature = "nonzero_negation_ops", since = "1.71.0")]
        #[rustc_const_stable(feature = "nonzero_negation_ops", since = "1.71.0")]
        pub const fn is_negative(self) -> bool {
            self.get().is_negative()
        }

        /// Checked negation. Computes `-self`,
        #[doc = concat!("returning `None` if `self == NonZero::<", stringify!($Int), ">::MIN`.")]
        ///
        /// # Example
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos_five = NonZero::new(5", stringify!($Int), ")?;")]
        #[doc = concat!("let neg_five = NonZero::new(-5", stringify!($Int), ")?;")]
        #[doc = concat!("let min = NonZero::new(", stringify!($Int), "::MIN)?;")]
        ///
        /// assert_eq!(pos_five.checked_neg(), Some(neg_five));
        /// assert_eq!(min.checked_neg(), None);
        /// # Some(())
        /// # }
        /// ```
        #[inline]
        #[stable(feature = "nonzero_negation_ops", since = "1.71.0")]
        #[rustc_const_stable(feature = "nonzero_negation_ops", since = "1.71.0")]
        // `None` exactly for `MIN` (the only overflowing input), else `Some(-self)`;
        // `-x` of nonzero is nonzero, discharging the internal `new_unchecked`.
        // `wrapping_neg` keeps the value clause itself overflow-free.
        #[ensures(|result: &Option<Self>| result.is_none() == (self.get() == <$Int>::MIN))]
        #[ensures(|result: &Option<Self>| result.is_none() || result.unwrap().get() == self.get().wrapping_neg())]
        pub const fn checked_neg(self) -> Option<Self> {
            if let Some(result) = self.get().checked_neg() {
                // SAFETY: negation of nonzero cannot yield zero values.
                return Some(unsafe { Self::new_unchecked(result) });
            }
            None
        }

        /// Negates self, overflowing if this is equal to the minimum value.
        ///
        #[doc = concat!("See [`", stringify!($Int), "::overflowing_neg`]")]
        /// for documentation on overflow behavior.
        ///
        /// # Example
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos_five = NonZero::new(5", stringify!($Int), ")?;")]
        #[doc = concat!("let neg_five = NonZero::new(-5", stringify!($Int), ")?;")]
        #[doc = concat!("let min = NonZero::new(", stringify!($Int), "::MIN)?;")]
        ///
        /// assert_eq!(pos_five.overflowing_neg(), (neg_five, false));
        /// assert_eq!(min.overflowing_neg(), (min, true));
        /// # Some(())
        /// # }
        /// ```
        #[inline]
        #[stable(feature = "nonzero_negation_ops", since = "1.71.0")]
        #[rustc_const_stable(feature = "nonzero_negation_ops", since = "1.71.0")]
        // The flag is exactly `self == MIN`; the value always equals
        // `self.wrapping_neg()`, which is nonzero for nonzero input, discharging the
        // internal `new_unchecked`. `wrapping_neg` keeps the value clause itself
        // overflow-free.
        #[ensures(|result: &(Self, bool)| result.1 == (self.get() == <$Int>::MIN))]
        #[ensures(|result: &(Self, bool)| result.0.get() == self.get().wrapping_neg())]
        pub const fn overflowing_neg(self) -> (Self, bool) {
            let (result, overflow) = self.get().overflowing_neg();
            // SAFETY: negation of nonzero cannot yield zero values.
            ((unsafe { Self::new_unchecked(result) }), overflow)
        }

        /// Saturating negation. Computes `-self`,
        #[doc = concat!("returning [`NonZero::<", stringify!($Int), ">::MAX`]")]
        #[doc = concat!("if `self == NonZero::<", stringify!($Int), ">::MIN`")]
        /// instead of overflowing.
        ///
        /// # Example
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos_five = NonZero::new(5", stringify!($Int), ")?;")]
        #[doc = concat!("let neg_five = NonZero::new(-5", stringify!($Int), ")?;")]
        #[doc = concat!("let min = NonZero::new(", stringify!($Int), "::MIN)?;")]
        #[doc = concat!("let min_plus_one = NonZero::new(", stringify!($Int), "::MIN + 1)?;")]
        #[doc = concat!("let max = NonZero::new(", stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(pos_five.saturating_neg(), neg_five);
        /// assert_eq!(min.saturating_neg(), max);
        /// assert_eq!(max.saturating_neg(), min_plus_one);
        /// # Some(())
        /// # }
        /// ```
        #[inline]
        #[stable(feature = "nonzero_negation_ops", since = "1.71.0")]
        #[rustc_const_stable(feature = "nonzero_negation_ops", since = "1.71.0")]
        pub const fn saturating_neg(self) -> Self {
            if let Some(result) = self.checked_neg() {
                return result;
            }
            Self::MAX
        }

        /// Wrapping (modular) negation. Computes `-self`, wrapping around at the boundary
        /// of the type.
        ///
        #[doc = concat!("See [`", stringify!($Int), "::wrapping_neg`]")]
        /// for documentation on overflow behavior.
        ///
        /// # Example
        ///
        /// ```
        /// # use std::num::NonZero;
        /// #
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos_five = NonZero::new(5", stringify!($Int), ")?;")]
        #[doc = concat!("let neg_five = NonZero::new(-5", stringify!($Int), ")?;")]
        #[doc = concat!("let min = NonZero::new(", stringify!($Int), "::MIN)?;")]
        ///
        /// assert_eq!(pos_five.wrapping_neg(), neg_five);
        /// assert_eq!(min.wrapping_neg(), min);
        /// # Some(())
        /// # }
        /// ```
        #[inline]
        #[stable(feature = "nonzero_negation_ops", since = "1.71.0")]
        #[rustc_const_stable(feature = "nonzero_negation_ops", since = "1.71.0")]
        // `-self` with `MIN` wrapping to `MIN`: never zero for nonzero input,
        // discharging the internal `new_unchecked`. `wrapping_neg` never overflows,
        // so no input assumption is needed.
        #[ensures(|result: &Self| result.get() == self.get().wrapping_neg())]
        pub const fn wrapping_neg(self) -> Self {
            let result = self.get().wrapping_neg();
            // SAFETY: negation of nonzero cannot yield zero values.
            unsafe { Self::new_unchecked(result) }
        }

        /// Returns the bit pattern of `self` reinterpreted as an unsigned integer of the same size.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::num::NonZero;
        ///
        #[doc = concat!("let n = NonZero::new(-1", stringify!($Int), ").unwrap();")]
        ///
        #[doc = concat!("assert_eq!(n.cast_unsigned(), NonZero::<", stringify!($Uint), ">::MAX);")]
        /// ```
        #[stable(feature = "integer_sign_cast", since = "1.87.0")]
        #[rustc_const_stable(feature = "integer_sign_cast", since = "1.87.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn cast_unsigned(self) -> NonZero<$Uint> {
            // SAFETY: `self.get()` can't be zero
            unsafe { NonZero::new_unchecked(self.get().cast_unsigned()) }
        }

    };
}

nonzero_integer! {
    Self = NonZeroU8,
    Primitive = unsigned u8,
    SignedPrimitive = i8,
    rot = 2,
    rot_op = "0x82",
    rot_result = "0xa",
    swap_op = "0x12",
    swapped = "0x12",
    reversed = "0x48",
}

nonzero_integer! {
    Self = NonZeroU16,
    Primitive = unsigned u16,
    SignedPrimitive = i16,
    rot = 4,
    rot_op = "0xa003",
    rot_result = "0x3a",
    swap_op = "0x1234",
    swapped = "0x3412",
    reversed = "0x2c48",
}

nonzero_integer! {
    Self = NonZeroU32,
    Primitive = unsigned u32,
    SignedPrimitive = i32,
    rot = 8,
    rot_op = "0x10000b3",
    rot_result = "0xb301",
    swap_op = "0x12345678",
    swapped = "0x78563412",
    reversed = "0x1e6a2c48",
}

nonzero_integer! {
    Self = NonZeroU64,
    Primitive = unsigned u64,
    SignedPrimitive = i64,
    rot = 12,
    rot_op = "0xaa00000000006e1",
    rot_result = "0x6e10aa",
    swap_op = "0x1234567890123456",
    swapped = "0x5634129078563412",
    reversed = "0x6a2c48091e6a2c48",
}

nonzero_integer! {
    Self = NonZeroU128,
    Primitive = unsigned u128,
    SignedPrimitive = i128,
    rot = 16,
    rot_op = "0x13f40000000000000000000000004f76",
    rot_result = "0x4f7613f4",
    swap_op = "0x12345678901234567890123456789012",
    swapped = "0x12907856341290785634129078563412",
    reversed = "0x48091e6a2c48091e6a2c48091e6a2c48",
}

#[cfg(target_pointer_width = "16")]
nonzero_integer! {
    Self = NonZeroUsize,
    Primitive = unsigned usize,
    SignedPrimitive = isize,
    rot = 4,
    rot_op = "0xa003",
    rot_result = "0x3a",
    swap_op = "0x1234",
    swapped = "0x3412",
    reversed = "0x2c48",
}

#[cfg(target_pointer_width = "32")]
nonzero_integer! {
    Self = NonZeroUsize,
    Primitive = unsigned usize,
    SignedPrimitive = isize,
    rot = 8,
    rot_op = "0x10000b3",
    rot_result = "0xb301",
    swap_op = "0x12345678",
    swapped = "0x78563412",
    reversed = "0x1e6a2c48",
}

#[cfg(target_pointer_width = "64")]
nonzero_integer! {
    Self = NonZeroUsize,
    Primitive = unsigned usize,
    SignedPrimitive = isize,
    rot = 12,
    rot_op = "0xaa00000000006e1",
    rot_result = "0x6e10aa",
    swap_op = "0x1234567890123456",
    swapped = "0x5634129078563412",
    reversed = "0x6a2c48091e6a2c48",
}

nonzero_integer! {
    Self = NonZeroI8,
    Primitive = signed i8,
    UnsignedPrimitive = u8,
    rot = 2,
    rot_op = "-0x7e",
    rot_result = "0xa",
    swap_op = "0x12",
    swapped = "0x12",
    reversed = "0x48",
}

nonzero_integer! {
    Self = NonZeroI16,
    Primitive = signed i16,
    UnsignedPrimitive = u16,
    rot = 4,
    rot_op = "-0x5ffd",
    rot_result = "0x3a",
    swap_op = "0x1234",
    swapped = "0x3412",
    reversed = "0x2c48",
}

nonzero_integer! {
    Self = NonZeroI32,
    Primitive = signed i32,
    UnsignedPrimitive = u32,
    rot = 8,
    rot_op = "0x10000b3",
    rot_result = "0xb301",
    swap_op = "0x12345678",
    swapped = "0x78563412",
    reversed = "0x1e6a2c48",
}

nonzero_integer! {
    Self = NonZeroI64,
    Primitive = signed i64,
    UnsignedPrimitive = u64,
    rot = 12,
    rot_op = "0xaa00000000006e1",
    rot_result = "0x6e10aa",
    swap_op = "0x1234567890123456",
    swapped = "0x5634129078563412",
    reversed = "0x6a2c48091e6a2c48",
}

nonzero_integer! {
    Self = NonZeroI128,
    Primitive = signed i128,
    UnsignedPrimitive = u128,
    rot = 16,
    rot_op = "0x13f40000000000000000000000004f76",
    rot_result = "0x4f7613f4",
    swap_op = "0x12345678901234567890123456789012",
    swapped = "0x12907856341290785634129078563412",
    reversed = "0x48091e6a2c48091e6a2c48091e6a2c48",
}

#[cfg(target_pointer_width = "16")]
nonzero_integer! {
    Self = NonZeroIsize,
    Primitive = signed isize,
    UnsignedPrimitive = usize,
    rot = 4,
    rot_op = "-0x5ffd",
    rot_result = "0x3a",
    swap_op = "0x1234",
    swapped = "0x3412",
    reversed = "0x2c48",
}

#[cfg(target_pointer_width = "32")]
nonzero_integer! {
    Self = NonZeroIsize,
    Primitive = signed isize,
    UnsignedPrimitive = usize,
    rot = 8,
    rot_op = "0x10000b3",
    rot_result = "0xb301",
    swap_op = "0x12345678",
    swapped = "0x78563412",
    reversed = "0x1e6a2c48",
}

#[cfg(target_pointer_width = "64")]
nonzero_integer! {
    Self = NonZeroIsize,
    Primitive = signed isize,
    UnsignedPrimitive = usize,
    rot = 12,
    rot_op = "0xaa00000000006e1",
    rot_result = "0x6e10aa",
    swap_op = "0x1234567890123456",
    swapped = "0x5634129078563412",
    reversed = "0x6a2c48091e6a2c48",
}

#[unstable(feature = "kani", issue = "none")]
#[cfg(kani)]
mod verify {
    use super::*;

    macro_rules! nonzero_check {
        ($t:ty, $nonzero_type:ty, $nonzero_check_new_unchecked_for:ident) => {
            #[kani::proof_for_contract(NonZero::new_unchecked)]
            pub fn $nonzero_check_new_unchecked_for() {
                let x: $t = kani::any(); // Generates a symbolic value of the provided type

                unsafe {
                    <$nonzero_type>::new_unchecked(x); // Calls NonZero::new_unchecked for the specified NonZero type
                }
            }
        };
    }

    // Use the macro to generate different versions of the function for multiple types
    nonzero_check!(i8, core::num::NonZeroI8, nonzero_check_new_unchecked_for_i8);
    nonzero_check!(i16, core::num::NonZeroI16, nonzero_check_new_unchecked_for_16);
    nonzero_check!(i32, core::num::NonZeroI32, nonzero_check_new_unchecked_for_32);
    nonzero_check!(i64, core::num::NonZeroI64, nonzero_check_new_unchecked_for_64);
    nonzero_check!(i128, core::num::NonZeroI128, nonzero_check_new_unchecked_for_128);
    nonzero_check!(isize, core::num::NonZeroIsize, nonzero_check_new_unchecked_for_isize);
    nonzero_check!(u8, core::num::NonZeroU8, nonzero_check_new_unchecked_for_u8);
    nonzero_check!(u16, core::num::NonZeroU16, nonzero_check_new_unchecked_for_u16);
    nonzero_check!(u32, core::num::NonZeroU32, nonzero_check_new_unchecked_for_u32);
    nonzero_check!(u64, core::num::NonZeroU64, nonzero_check_new_unchecked_for_u64);
    nonzero_check!(u128, core::num::NonZeroU128, nonzero_check_new_unchecked_for_u128);
    nonzero_check!(usize, core::num::NonZeroUsize, nonzero_check_new_unchecked_for_usize);

    // `new` harnesses: the contract checks the layout precondition backing the
    // body's `transmute_unchecked` (`size_of::<T>() == size_of::<Option<Self>>()`),
    // that a `NonZero` is produced iff the input is nonzero, and that the inner
    // value equals the input. Full input domain (zero included) per width.
    macro_rules! nonzero_check_new {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::new)]
            pub fn $harness_name() {
                let x: $t = kani::any();
                let _ = <$nonzero_type>::new(x);
            }
        };
    }

    nonzero_check_new!(i8, core::num::NonZeroI8, nonzero_check_new_for_i8);
    nonzero_check_new!(i16, core::num::NonZeroI16, nonzero_check_new_for_i16);
    nonzero_check_new!(i32, core::num::NonZeroI32, nonzero_check_new_for_i32);
    nonzero_check_new!(i64, core::num::NonZeroI64, nonzero_check_new_for_i64);
    nonzero_check_new!(i128, core::num::NonZeroI128, nonzero_check_new_for_i128);
    nonzero_check_new!(isize, core::num::NonZeroIsize, nonzero_check_new_for_isize);
    nonzero_check_new!(u8, core::num::NonZeroU8, nonzero_check_new_for_u8);
    nonzero_check_new!(u16, core::num::NonZeroU16, nonzero_check_new_for_u16);
    nonzero_check_new!(u32, core::num::NonZeroU32, nonzero_check_new_for_u32);
    nonzero_check_new!(u64, core::num::NonZeroU64, nonzero_check_new_for_u64);
    nonzero_check_new!(u128, core::num::NonZeroU128, nonzero_check_new_for_u128);
    nonzero_check_new!(usize, core::num::NonZeroUsize, nonzero_check_new_for_usize);

    macro_rules! nonzero_check_from_mut_unchecked {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::from_mut_unchecked)]
            pub fn $harness_name() {
                let mut x: $t = kani::any();
                unsafe {
                    <$nonzero_type>::from_mut_unchecked(&mut x);
                }
            }
        };
    }

    // Generate harnesses for multiple types
    nonzero_check_from_mut_unchecked!(
        i8,
        core::num::NonZeroI8,
        nonzero_check_from_mut_unchecked_i8
    );
    nonzero_check_from_mut_unchecked!(
        i16,
        core::num::NonZeroI16,
        nonzero_check_from_mut_unchecked_i16
    );
    nonzero_check_from_mut_unchecked!(
        i32,
        core::num::NonZeroI32,
        nonzero_check_from_mut_unchecked_i32
    );
    nonzero_check_from_mut_unchecked!(
        i64,
        core::num::NonZeroI64,
        nonzero_check_from_mut_unchecked_i64
    );
    nonzero_check_from_mut_unchecked!(
        i128,
        core::num::NonZeroI128,
        nonzero_check_from_mut_unchecked_i128
    );
    nonzero_check_from_mut_unchecked!(
        isize,
        core::num::NonZeroIsize,
        nonzero_check_from_mut_unchecked_isize
    );
    nonzero_check_from_mut_unchecked!(
        u8,
        core::num::NonZeroU8,
        nonzero_check_from_mut_unchecked_u8
    );
    nonzero_check_from_mut_unchecked!(
        u16,
        core::num::NonZeroU16,
        nonzero_check_from_mut_unchecked_u16
    );
    nonzero_check_from_mut_unchecked!(
        u32,
        core::num::NonZeroU32,
        nonzero_check_from_mut_unchecked_u32
    );
    nonzero_check_from_mut_unchecked!(
        u64,
        core::num::NonZeroU64,
        nonzero_check_from_mut_unchecked_u64
    );
    nonzero_check_from_mut_unchecked!(
        u128,
        core::num::NonZeroU128,
        nonzero_check_from_mut_unchecked_u128
    );
    nonzero_check_from_mut_unchecked!(
        usize,
        core::num::NonZeroUsize,
        nonzero_check_from_mut_unchecked_usize
    );

    // `from_mut` harnesses: verify the unsafe reborrow through the raw-pointer
    // cast (Kani's memory checks are always on) and the `new`-equivalent
    // correctness properties. In-body assertions instead of `#[ensures]`: the
    // returned `Option<&mut Self>` mutably aliases the input, so a contract
    // reading both would be an aliasing hazard. Full input domain per width.
    macro_rules! nonzero_check_from_mut {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof]
            pub fn $harness_name() {
                let mut x: $t = kani::any();
                let orig = x;
                let result = <$nonzero_type>::from_mut(&mut x);
                match result {
                    Some(nz) => {
                        // A NonZero is produced only when the input was nonzero,
                        // and it preserves the referenced value.
                        assert!(orig != 0);
                        assert!(nz.get() == orig);
                    }
                    None => {
                        // `None` is produced exactly when the input was zero.
                        assert!(orig == 0);
                    }
                }
            }
        };
    }

    nonzero_check_from_mut!(i8, core::num::NonZeroI8, nonzero_check_from_mut_i8);
    nonzero_check_from_mut!(i16, core::num::NonZeroI16, nonzero_check_from_mut_i16);
    nonzero_check_from_mut!(i32, core::num::NonZeroI32, nonzero_check_from_mut_i32);
    nonzero_check_from_mut!(i64, core::num::NonZeroI64, nonzero_check_from_mut_i64);
    nonzero_check_from_mut!(i128, core::num::NonZeroI128, nonzero_check_from_mut_i128);
    nonzero_check_from_mut!(isize, core::num::NonZeroIsize, nonzero_check_from_mut_isize);
    nonzero_check_from_mut!(u8, core::num::NonZeroU8, nonzero_check_from_mut_u8);
    nonzero_check_from_mut!(u16, core::num::NonZeroU16, nonzero_check_from_mut_u16);
    nonzero_check_from_mut!(u32, core::num::NonZeroU32, nonzero_check_from_mut_u32);
    nonzero_check_from_mut!(u64, core::num::NonZeroU64, nonzero_check_from_mut_u64);
    nonzero_check_from_mut!(u128, core::num::NonZeroU128, nonzero_check_from_mut_u128);
    nonzero_check_from_mut!(usize, core::num::NonZeroUsize, nonzero_check_from_mut_usize);

    macro_rules! nonzero_check_cmp {
        ($nonzero_type:ty, $nonzero_check_cmp_for:ident) => {
            #[kani::proof]
            pub fn $nonzero_check_cmp_for() {
                let x: $nonzero_type = kani::any();
                let y: $nonzero_type = kani::any();
                if x < y {
                    assert!(x.cmp(&y) == core::cmp::Ordering::Less);
                } else if x > y {
                    assert!(x.cmp(&y) == core::cmp::Ordering::Greater);
                } else {
                    assert!(x.cmp(&y) == core::cmp::Ordering::Equal);
                }
            }
        };
    }

    // Use the macro to generate different versions of the function for multiple types
    nonzero_check_cmp!(core::num::NonZeroI8, nonzero_check_cmp_for_i8);
    nonzero_check_cmp!(core::num::NonZeroI16, nonzero_check_cmp_for_i16);
    nonzero_check_cmp!(core::num::NonZeroI32, nonzero_check_cmp_for_i32);
    nonzero_check_cmp!(core::num::NonZeroI64, nonzero_check_cmp_for_i64);
    nonzero_check_cmp!(core::num::NonZeroI128, nonzero_check_cmp_for_i128);
    nonzero_check_cmp!(core::num::NonZeroIsize, nonzero_check_cmp_for_isize);
    nonzero_check_cmp!(core::num::NonZeroU8, nonzero_check_cmp_for_u8);
    nonzero_check_cmp!(core::num::NonZeroU16, nonzero_check_cmp_for_u16);
    nonzero_check_cmp!(core::num::NonZeroU32, nonzero_check_cmp_for_u32);
    nonzero_check_cmp!(core::num::NonZeroU64, nonzero_check_cmp_for_u64);
    nonzero_check_cmp!(core::num::NonZeroU128, nonzero_check_cmp_for_u128);
    nonzero_check_cmp!(core::num::NonZeroUsize, nonzero_check_cmp_for_usize);

    macro_rules! nonzero_check_max {
        ($nonzero_type:ty, $nonzero_check_max_for:ident) => {
            #[kani::proof]
            pub fn $nonzero_check_max_for() {
                let x: $nonzero_type = kani::any();
                let y: $nonzero_type = kani::any();
                let result = x.max(y);
                if x > y {
                    assert!(result == x);
                } else {
                    assert!(result == y);
                }
            }
        };
    }

    nonzero_check_max!(core::num::NonZeroI8, nonzero_check_max_for_i8);
    nonzero_check_max!(core::num::NonZeroI16, nonzero_check_max_for_i16);
    nonzero_check_max!(core::num::NonZeroI32, nonzero_check_max_for_i32);
    nonzero_check_max!(core::num::NonZeroI64, nonzero_check_max_for_i64);
    nonzero_check_max!(core::num::NonZeroI128, nonzero_check_max_for_i128);
    nonzero_check_max!(core::num::NonZeroIsize, nonzero_check_max_for_isize);
    nonzero_check_max!(core::num::NonZeroU8, nonzero_check_max_for_u8);
    nonzero_check_max!(core::num::NonZeroU16, nonzero_check_max_for_u16);
    nonzero_check_max!(core::num::NonZeroU32, nonzero_check_max_for_u32);
    nonzero_check_max!(core::num::NonZeroU64, nonzero_check_max_for_u64);
    nonzero_check_max!(core::num::NonZeroU128, nonzero_check_max_for_u128);
    nonzero_check_max!(core::num::NonZeroUsize, nonzero_check_max_for_usize);

    macro_rules! nonzero_check_min {
        ($nonzero_type:ty, $nonzero_check_min_for:ident) => {
            #[kani::proof]
            pub fn $nonzero_check_min_for() {
                let x: $nonzero_type = kani::any();
                let y: $nonzero_type = kani::any();
                let result = x.min(y);
                if x < y {
                    assert!(result == x);
                } else {
                    assert!(result == y);
                }
            }
        };
    }

    nonzero_check_min!(core::num::NonZeroI8, nonzero_check_min_for_i8);
    nonzero_check_min!(core::num::NonZeroI16, nonzero_check_min_for_i16);
    nonzero_check_min!(core::num::NonZeroI32, nonzero_check_min_for_i32);
    nonzero_check_min!(core::num::NonZeroI64, nonzero_check_min_for_i64);
    nonzero_check_min!(core::num::NonZeroI128, nonzero_check_min_for_i128);
    nonzero_check_min!(core::num::NonZeroIsize, nonzero_check_min_for_isize);
    nonzero_check_min!(core::num::NonZeroU8, nonzero_check_min_for_u8);
    nonzero_check_min!(core::num::NonZeroU16, nonzero_check_min_for_u16);
    nonzero_check_min!(core::num::NonZeroU32, nonzero_check_min_for_u32);
    nonzero_check_min!(core::num::NonZeroU64, nonzero_check_min_for_u64);
    nonzero_check_min!(core::num::NonZeroU128, nonzero_check_min_for_u128);
    nonzero_check_min!(core::num::NonZeroUsize, nonzero_check_min_for_usize);

    macro_rules! nonzero_check_clamp {
        ($nonzero_type:ty, $nonzero_check_clamp_for:ident) => {
            #[kani::proof]
            pub fn $nonzero_check_clamp_for() {
                let x: $nonzero_type = kani::any();
                let min: $nonzero_type = kani::any();
                let max: $nonzero_type = kani::any();
                // Ensure min <= max, so the function should no panic
                kani::assume(min <= max);
                kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
                // Use the clamp function and check the result
                let result = x.clamp(min, max);
                if x < min {
                    assert!(result == min);
                } else if x > max {
                    assert!(result == max);
                } else {
                    assert!(result == x);
                }
            }
        };
    }

    // Use the macro to generate different versions of the function for multiple types
    nonzero_check_clamp!(core::num::NonZeroI8, nonzero_check_clamp_for_i8);
    nonzero_check_clamp!(core::num::NonZeroI16, nonzero_check_clamp_for_16);
    nonzero_check_clamp!(core::num::NonZeroI32, nonzero_check_clamp_for_32);
    nonzero_check_clamp!(core::num::NonZeroI64, nonzero_check_clamp_for_64);
    nonzero_check_clamp!(core::num::NonZeroI128, nonzero_check_clamp_for_128);
    nonzero_check_clamp!(core::num::NonZeroIsize, nonzero_check_clamp_for_isize);
    nonzero_check_clamp!(core::num::NonZeroU8, nonzero_check_clamp_for_u8);
    nonzero_check_clamp!(core::num::NonZeroU16, nonzero_check_clamp_for_u16);
    nonzero_check_clamp!(core::num::NonZeroU32, nonzero_check_clamp_for_u32);
    nonzero_check_clamp!(core::num::NonZeroU64, nonzero_check_clamp_for_u64);
    nonzero_check_clamp!(core::num::NonZeroU128, nonzero_check_clamp_for_u128);
    nonzero_check_clamp!(core::num::NonZeroUsize, nonzero_check_clamp_for_usize);

    macro_rules! nonzero_check_clamp_panic {
        ($nonzero_type:ty, $nonzero_check_clamp_for:ident) => {
            #[kani::proof]
            #[kani::should_panic]
            pub fn $nonzero_check_clamp_for() {
                let x: $nonzero_type = kani::any();
                let min: $nonzero_type = kani::any();
                let max: $nonzero_type = kani::any();
                // Ensure min > max, so the function should panic
                kani::assume(min > max);
                kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
                // Use the clamp function and check the result
                let result = x.clamp(min, max);
                if x < min {
                    assert!(result == min);
                } else if x > max {
                    assert!(result == max);
                } else {
                    assert!(result == x);
                }
            }
        };
    }

    // Use the macro to generate different versions of the function for multiple types
    nonzero_check_clamp_panic!(core::num::NonZeroI8, nonzero_check_clamp_panic_for_i8);
    nonzero_check_clamp_panic!(core::num::NonZeroI16, nonzero_check_clamp_panic_for_16);
    nonzero_check_clamp_panic!(core::num::NonZeroI32, nonzero_check_clamp_panic_for_32);
    nonzero_check_clamp_panic!(core::num::NonZeroI64, nonzero_check_clamp_panic_for_64);
    nonzero_check_clamp_panic!(core::num::NonZeroI128, nonzero_check_clamp_panic_for_128);
    nonzero_check_clamp_panic!(core::num::NonZeroIsize, nonzero_check_clamp_panic_for_isize);
    nonzero_check_clamp_panic!(core::num::NonZeroU8, nonzero_check_clamp_panic_for_u8);
    nonzero_check_clamp_panic!(core::num::NonZeroU16, nonzero_check_clamp_panic_for_u16);
    nonzero_check_clamp_panic!(core::num::NonZeroU32, nonzero_check_clamp_panic_for_u32);
    nonzero_check_clamp_panic!(core::num::NonZeroU64, nonzero_check_clamp_panic_for_u64);
    nonzero_check_clamp_panic!(core::num::NonZeroU128, nonzero_check_clamp_panic_for_u128);
    nonzero_check_clamp_panic!(core::num::NonZeroUsize, nonzero_check_clamp_panic_for_usize);

    macro_rules! check_mul_unchecked_small {
        ($t:ty, $nonzero_type:ty, $nonzero_check_unchecked_mul_for:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::unchecked_mul)]
            pub fn $nonzero_check_unchecked_mul_for() {
                let x: $nonzero_type = kani::any();
                let y: $nonzero_type = kani::any();

                unsafe {
                    x.unchecked_mul(y);
                }
            }
        };
    }

    // `unchecked_mul` interval harnesses (pattern from num/mod.rs). Two
    // vacuity guards: the extreme intervals are paired with a small
    // counter-operand interval (same-interval extreme pairs always overflow,
    // making the assumed `#[requires(checked_mul(..).is_some())]`
    // unsatisfiable and the harness vacuous), and the `kani::cover` witnesses
    // that precondition itself, so a pairing with no valid input fails loudly
    // instead of verifying vacuously.
    macro_rules! check_mul_unchecked_intervals {
        ($t:ty, $nonzero_type:ty, $nonzero_check_mul_for:ident,
         $xmin:expr, $xmax:expr, $ymin:expr, $ymax:expr) => {
            #[kani::proof_for_contract(NonZero::<$t>::unchecked_mul)]
            pub fn $nonzero_check_mul_for() {
                let x = kani::any::<$t>();
                let y = kani::any::<$t>();

                // Vacuity guard: inverted endpoints would make the assumes
                // unsatisfiable; assert before assuming so it fails loudly.
                let (__x_min, __x_max): ($t, $t) = ($xmin, $xmax);
                assert!(__x_min <= __x_max, "x interval endpoints inverted");
                let (__y_min, __y_max): ($t, $t) = ($ymin, $ymax);
                assert!(__y_min <= __y_max, "y interval endpoints inverted");
                kani::assume(x != 0 && x >= $xmin && x <= $xmax);
                kani::assume(y != 0 && y >= $ymin && y <= $ymax);
                kani::cover(
                    x.checked_mul(y).is_some(),
                    "non-vacuity witness: a pair satisfying unchecked_mul's precondition exists",
                );

                let x = <$nonzero_type>::new(x).unwrap();
                let y = <$nonzero_type>::new(y).unwrap();

                unsafe {
                    x.unchecked_mul(y);
                }
            }
        };
    }

    // Signed widths: a symmetric small×small harness, plus each extreme
    // interval (near-MAX, near-MIN, and the half-range edges) × a small
    // counter-operand interval (so |y| == 1 keeps the product in range and
    // the precondition satisfiable).
    macro_rules! check_mul_unchecked_intervals_signed {
        ($t:ty, $nonzero_type:ty, $small:ident, $large_pos:ident, $large_neg:ident,
         $edge_pos:ident, $edge_neg:ident) => {
            check_mul_unchecked_intervals!($t, $nonzero_type, $small, -10, 10, -10, 10);
            check_mul_unchecked_intervals!(
                $t,
                $nonzero_type,
                $large_pos,
                <$t>::MAX - 1000,
                <$t>::MAX,
                -10,
                10
            );
            check_mul_unchecked_intervals!(
                $t,
                $nonzero_type,
                $large_neg,
                <$t>::MIN + 1,
                <$t>::MIN + 1000,
                -10,
                10
            );
            check_mul_unchecked_intervals!(
                $t,
                $nonzero_type,
                $edge_pos,
                <$t>::MAX / 2,
                <$t>::MAX,
                -10,
                10
            );
            check_mul_unchecked_intervals!(
                $t,
                $nonzero_type,
                $edge_neg,
                <$t>::MIN + 1,
                <$t>::MIN / 2,
                -10,
                10
            );
        };
    }

    // Unsigned widths: small×small, plus near-MAX and half-range-edge
    // intervals × a small counter-operand interval (y == 1 keeps the product
    // in range and the precondition satisfiable).
    macro_rules! check_mul_unchecked_intervals_unsigned {
        ($t:ty, $nonzero_type:ty, $small:ident, $large:ident, $edge:ident) => {
            check_mul_unchecked_intervals!($t, $nonzero_type, $small, 1, 10, 1, 10);
            check_mul_unchecked_intervals!(
                $t,
                $nonzero_type,
                $large,
                <$t>::MAX - 1000,
                <$t>::MAX,
                1,
                10
            );
            check_mul_unchecked_intervals!(
                $t,
                $nonzero_type,
                $edge,
                <$t>::MAX / 2,
                <$t>::MAX,
                1,
                10
            );
        };
    }

    check_mul_unchecked_intervals_signed!(
        i32,
        NonZeroI32,
        check_mul_i32_small,
        check_mul_i32_large_pos,
        check_mul_i32_large_neg,
        check_mul_i32_edge_pos,
        check_mul_i32_edge_neg
    );
    check_mul_unchecked_intervals_signed!(
        i64,
        NonZeroI64,
        check_mul_i64_small,
        check_mul_i64_large_pos,
        check_mul_i64_large_neg,
        check_mul_i64_edge_pos,
        check_mul_i64_edge_neg
    );
    check_mul_unchecked_intervals_signed!(
        i128,
        NonZeroI128,
        check_mul_i128_small,
        check_mul_i128_large_pos,
        check_mul_i128_large_neg,
        check_mul_i128_edge_pos,
        check_mul_i128_edge_neg
    );
    check_mul_unchecked_intervals_signed!(
        isize,
        NonZeroIsize,
        check_mul_isize_small,
        check_mul_isize_large_pos,
        check_mul_isize_large_neg,
        check_mul_isize_edge_pos,
        check_mul_isize_edge_neg
    );

    check_mul_unchecked_intervals_unsigned!(
        u32,
        NonZeroU32,
        check_mul_u32_small,
        check_mul_u32_large,
        check_mul_u32_edge
    );
    check_mul_unchecked_intervals_unsigned!(
        u64,
        NonZeroU64,
        check_mul_u64_small,
        check_mul_u64_large,
        check_mul_u64_edge
    );
    check_mul_unchecked_intervals_unsigned!(
        u128,
        NonZeroU128,
        check_mul_u128_small,
        check_mul_u128_large,
        check_mul_u128_edge
    );
    check_mul_unchecked_intervals_unsigned!(
        usize,
        NonZeroUsize,
        check_mul_usize_small,
        check_mul_usize_large,
        check_mul_usize_edge
    );

    //calls for i8, i16, u8, u16
    check_mul_unchecked_small!(i8, NonZeroI8, nonzero_check_mul_for_i8);
    check_mul_unchecked_small!(i16, NonZeroI16, nonzero_check_mul_for_i16);
    check_mul_unchecked_small!(u8, NonZeroU8, nonzero_check_mul_for_u8);
    check_mul_unchecked_small!(u16, NonZeroU16, nonzero_check_mul_for_u16);

    // `checked_mul` harnesses: verify the contract (`Some` iff no overflow, with
    // the exact product) and, with it, the internal `new_unchecked`. Small types
    // get the full domain; wider types use bounded intervals to keep the
    // multiplication tractable for CBMC (`unchecked_mul` pattern above).
    macro_rules! nonzero_check_checked_mul_small {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::checked_mul)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let y: $nonzero_type = kani::any();
                let _ = x.checked_mul(y);
            }
        };
    }

    macro_rules! nonzero_check_checked_mul_intervals {
        ($t:ty, $nonzero_type:ty, $harness_name:ident, $min:expr, $max:expr) => {
            #[kani::proof_for_contract(NonZero::<$t>::checked_mul)]
            pub fn $harness_name() {
                let x = kani::any::<$t>();
                let y = kani::any::<$t>();

                // Vacuity guard: inverted endpoints would make the assume(s)
                // unsatisfiable; assert before assuming so it fails loudly.
                let (__ival_min, __ival_max): ($t, $t) = ($min, $max);
                assert!(__ival_min <= __ival_max, "interval endpoints inverted");
                kani::assume(x != 0 && x >= $min && x <= $max);
                kani::assume(y != 0 && y >= $min && y <= $max);
                kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");

                let x = <$nonzero_type>::new(x).unwrap();
                let y = <$nonzero_type>::new(y).unwrap();

                let _ = x.checked_mul(y);
            }
        };
    }

    // Small types: full input domain.
    nonzero_check_checked_mul_small!(i8, NonZeroI8, nonzero_check_checked_mul_for_i8);
    nonzero_check_checked_mul_small!(i16, NonZeroI16, nonzero_check_checked_mul_for_i16);
    nonzero_check_checked_mul_small!(u8, NonZeroU8, nonzero_check_checked_mul_for_u8);
    nonzero_check_checked_mul_small!(u16, NonZeroU16, nonzero_check_checked_mul_for_u16);

    // i32 intervals
    nonzero_check_checked_mul_intervals!(
        i32,
        NonZeroI32,
        nonzero_check_checked_mul_i32_small,
        NonZeroI32::new(-10i32).unwrap().into(),
        NonZeroI32::new(10i32).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        i32,
        NonZeroI32,
        nonzero_check_checked_mul_i32_large_pos,
        NonZeroI32::new(i32::MAX - 1000i32).unwrap().into(),
        NonZeroI32::new(i32::MAX).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        i32,
        NonZeroI32,
        nonzero_check_checked_mul_i32_large_neg,
        NonZeroI32::new(i32::MIN + 1).unwrap().into(),
        NonZeroI32::new(i32::MIN + 1000i32).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        i32,
        NonZeroI32,
        nonzero_check_checked_mul_i32_edge_pos,
        NonZeroI32::new(i32::MAX / 2).unwrap().into(),
        NonZeroI32::new(i32::MAX).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        i32,
        NonZeroI32,
        nonzero_check_checked_mul_i32_edge_neg,
        NonZeroI32::new(i32::MIN + 1).unwrap().into(),
        NonZeroI32::new(i32::MIN / 2).unwrap().into()
    );

    // i64 intervals
    nonzero_check_checked_mul_intervals!(
        i64,
        NonZeroI64,
        nonzero_check_checked_mul_i64_small,
        NonZeroI64::new(-10i64).unwrap().into(),
        NonZeroI64::new(10i64).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        i64,
        NonZeroI64,
        nonzero_check_checked_mul_i64_large_pos,
        NonZeroI64::new(i64::MAX - 1000i64).unwrap().into(),
        NonZeroI64::new(i64::MAX).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        i64,
        NonZeroI64,
        nonzero_check_checked_mul_i64_large_neg,
        NonZeroI64::new(i64::MIN + 1).unwrap().into(),
        NonZeroI64::new(i64::MIN + 1000i64).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        i64,
        NonZeroI64,
        nonzero_check_checked_mul_i64_edge_pos,
        NonZeroI64::new(i64::MAX / 2).unwrap().into(),
        NonZeroI64::new(i64::MAX).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        i64,
        NonZeroI64,
        nonzero_check_checked_mul_i64_edge_neg,
        NonZeroI64::new(i64::MIN + 1).unwrap().into(),
        NonZeroI64::new(i64::MIN / 2).unwrap().into()
    );

    // i128 intervals
    nonzero_check_checked_mul_intervals!(
        i128,
        NonZeroI128,
        nonzero_check_checked_mul_i128_small,
        NonZeroI128::new(-10i128).unwrap().into(),
        NonZeroI128::new(10i128).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        i128,
        NonZeroI128,
        nonzero_check_checked_mul_i128_large_pos,
        NonZeroI128::new(i128::MAX - 1000i128).unwrap().into(),
        NonZeroI128::new(i128::MAX).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        i128,
        NonZeroI128,
        nonzero_check_checked_mul_i128_large_neg,
        NonZeroI128::new(i128::MIN + 1).unwrap().into(),
        NonZeroI128::new(i128::MIN + 1000i128).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        i128,
        NonZeroI128,
        nonzero_check_checked_mul_i128_edge_pos,
        NonZeroI128::new(i128::MAX / 2).unwrap().into(),
        NonZeroI128::new(i128::MAX).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        i128,
        NonZeroI128,
        nonzero_check_checked_mul_i128_edge_neg,
        NonZeroI128::new(i128::MIN + 1).unwrap().into(),
        NonZeroI128::new(i128::MIN / 2).unwrap().into()
    );

    // isize intervals
    nonzero_check_checked_mul_intervals!(
        isize,
        NonZeroIsize,
        nonzero_check_checked_mul_isize_small,
        NonZeroIsize::new(-10isize).unwrap().into(),
        NonZeroIsize::new(10isize).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        isize,
        NonZeroIsize,
        nonzero_check_checked_mul_isize_large_pos,
        NonZeroIsize::new(isize::MAX - 1000isize).unwrap().into(),
        NonZeroIsize::new(isize::MAX).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        isize,
        NonZeroIsize,
        nonzero_check_checked_mul_isize_large_neg,
        NonZeroIsize::new(isize::MIN + 1).unwrap().into(),
        NonZeroIsize::new(isize::MIN + 1000isize).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        isize,
        NonZeroIsize,
        nonzero_check_checked_mul_isize_edge_pos,
        NonZeroIsize::new(isize::MAX / 2).unwrap().into(),
        NonZeroIsize::new(isize::MAX).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        isize,
        NonZeroIsize,
        nonzero_check_checked_mul_isize_edge_neg,
        NonZeroIsize::new(isize::MIN + 1).unwrap().into(),
        NonZeroIsize::new(isize::MIN / 2).unwrap().into()
    );

    // u32 intervals
    nonzero_check_checked_mul_intervals!(
        u32,
        NonZeroU32,
        nonzero_check_checked_mul_u32_small,
        NonZeroU32::new(1u32).unwrap().into(),
        NonZeroU32::new(10u32).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        u32,
        NonZeroU32,
        nonzero_check_checked_mul_u32_large,
        NonZeroU32::new(u32::MAX - 1000u32).unwrap().into(),
        NonZeroU32::new(u32::MAX).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        u32,
        NonZeroU32,
        nonzero_check_checked_mul_u32_edge,
        NonZeroU32::new(u32::MAX / 2).unwrap().into(),
        NonZeroU32::new(u32::MAX).unwrap().into()
    );

    // u64 intervals
    nonzero_check_checked_mul_intervals!(
        u64,
        NonZeroU64,
        nonzero_check_checked_mul_u64_small,
        NonZeroU64::new(1u64).unwrap().into(),
        NonZeroU64::new(10u64).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        u64,
        NonZeroU64,
        nonzero_check_checked_mul_u64_large,
        NonZeroU64::new(u64::MAX - 1000u64).unwrap().into(),
        NonZeroU64::new(u64::MAX).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        u64,
        NonZeroU64,
        nonzero_check_checked_mul_u64_edge,
        NonZeroU64::new(u64::MAX / 2).unwrap().into(),
        NonZeroU64::new(u64::MAX).unwrap().into()
    );

    // u128 intervals
    nonzero_check_checked_mul_intervals!(
        u128,
        NonZeroU128,
        nonzero_check_checked_mul_u128_small,
        NonZeroU128::new(1u128).unwrap().into(),
        NonZeroU128::new(10u128).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        u128,
        NonZeroU128,
        nonzero_check_checked_mul_u128_large,
        NonZeroU128::new(u128::MAX - 1000u128).unwrap().into(),
        NonZeroU128::new(u128::MAX).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        u128,
        NonZeroU128,
        nonzero_check_checked_mul_u128_edge,
        NonZeroU128::new(u128::MAX / 2).unwrap().into(),
        NonZeroU128::new(u128::MAX).unwrap().into()
    );

    // usize intervals
    nonzero_check_checked_mul_intervals!(
        usize,
        NonZeroUsize,
        nonzero_check_checked_mul_usize_small,
        NonZeroUsize::new(1usize).unwrap().into(),
        NonZeroUsize::new(10usize).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        usize,
        NonZeroUsize,
        nonzero_check_checked_mul_usize_large,
        NonZeroUsize::new(usize::MAX - 1000usize).unwrap().into(),
        NonZeroUsize::new(usize::MAX).unwrap().into()
    );
    nonzero_check_checked_mul_intervals!(
        usize,
        NonZeroUsize,
        nonzero_check_checked_mul_usize_edge,
        NonZeroUsize::new(usize::MAX / 2).unwrap().into(),
        NonZeroUsize::new(usize::MAX).unwrap().into()
    );

    // `checked_pow` harnesses: full base and exponent domain on every width,
    // unbounded. Under `-Z loop-contracts` the pow loop is abstracted by its
    // `safety::loop_invariant`, so no exponent bound, `#[kani::unwind]`, or
    // interval split is needed — but only invariant-derived facts (nonzero-ness)
    // are provable about the result, which is why the contract states no
    // exact-value clause.
    macro_rules! nonzero_check_checked_pow {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::checked_pow)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let exp: u32 = kani::any();
                let _ = x.checked_pow(exp);
            }
        };
    }

    nonzero_check_checked_pow!(i8, NonZeroI8, nonzero_check_checked_pow_for_i8);
    nonzero_check_checked_pow!(i16, NonZeroI16, nonzero_check_checked_pow_for_i16);
    nonzero_check_checked_pow!(i32, NonZeroI32, nonzero_check_checked_pow_for_i32);
    nonzero_check_checked_pow!(i64, NonZeroI64, nonzero_check_checked_pow_for_i64);
    nonzero_check_checked_pow!(i128, NonZeroI128, nonzero_check_checked_pow_for_i128);
    nonzero_check_checked_pow!(isize, NonZeroIsize, nonzero_check_checked_pow_for_isize);
    nonzero_check_checked_pow!(u8, NonZeroU8, nonzero_check_checked_pow_for_u8);
    nonzero_check_checked_pow!(u16, NonZeroU16, nonzero_check_checked_pow_for_u16);
    nonzero_check_checked_pow!(u32, NonZeroU32, nonzero_check_checked_pow_for_u32);
    nonzero_check_checked_pow!(u64, NonZeroU64, nonzero_check_checked_pow_for_u64);
    nonzero_check_checked_pow!(u128, NonZeroU128, nonzero_check_checked_pow_for_u128);
    nonzero_check_checked_pow!(usize, NonZeroUsize, nonzero_check_checked_pow_for_usize);

    // `saturating_pow` harnesses: full base and exponent domain on every width,
    // unbounded — same loop-abstraction setup and exact-value trade-off as
    // `checked_pow` above (`saturating_pow` delegates to the same loop).
    macro_rules! nonzero_check_saturating_pow {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::saturating_pow)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let exp: u32 = kani::any();
                let _ = x.saturating_pow(exp);
            }
        };
    }

    nonzero_check_saturating_pow!(i8, NonZeroI8, nonzero_check_saturating_pow_for_i8);
    nonzero_check_saturating_pow!(i16, NonZeroI16, nonzero_check_saturating_pow_for_i16);
    nonzero_check_saturating_pow!(i32, NonZeroI32, nonzero_check_saturating_pow_for_i32);
    nonzero_check_saturating_pow!(i64, NonZeroI64, nonzero_check_saturating_pow_for_i64);
    nonzero_check_saturating_pow!(i128, NonZeroI128, nonzero_check_saturating_pow_for_i128);
    nonzero_check_saturating_pow!(isize, NonZeroIsize, nonzero_check_saturating_pow_for_isize);
    nonzero_check_saturating_pow!(u8, NonZeroU8, nonzero_check_saturating_pow_for_u8);
    nonzero_check_saturating_pow!(u16, NonZeroU16, nonzero_check_saturating_pow_for_u16);
    nonzero_check_saturating_pow!(u32, NonZeroU32, nonzero_check_saturating_pow_for_u32);
    nonzero_check_saturating_pow!(u64, NonZeroU64, nonzero_check_saturating_pow_for_u64);
    nonzero_check_saturating_pow!(u128, NonZeroU128, nonzero_check_saturating_pow_for_u128);
    nonzero_check_saturating_pow!(usize, NonZeroUsize, nonzero_check_saturating_pow_for_usize);

    // `saturating_mul` harnesses: verify the contract (exact
    // `$Int::saturating_mul` value; nonzero since the saturation bounds are
    // nonzero) and, with it, the internal `new_unchecked`. Small types get the
    // full domain; wider types use bounded intervals (`checked_mul` pattern).
    macro_rules! nonzero_check_saturating_mul_small {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::saturating_mul)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let y: $nonzero_type = kani::any();
                let _ = x.saturating_mul(y);
            }
        };
    }

    macro_rules! nonzero_check_saturating_mul_intervals {
        ($t:ty, $nonzero_type:ty, $harness_name:ident, $min:expr, $max:expr) => {
            #[kani::proof_for_contract(NonZero::<$t>::saturating_mul)]
            pub fn $harness_name() {
                let x = kani::any::<$t>();
                let y = kani::any::<$t>();

                // Vacuity guard: inverted endpoints would make the assume(s)
                // unsatisfiable; assert before assuming so it fails loudly.
                let (__ival_min, __ival_max): ($t, $t) = ($min, $max);
                assert!(__ival_min <= __ival_max, "interval endpoints inverted");
                kani::assume(x != 0 && x >= $min && x <= $max);
                kani::assume(y != 0 && y >= $min && y <= $max);
                kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");

                let x = <$nonzero_type>::new(x).unwrap();
                let y = <$nonzero_type>::new(y).unwrap();

                let _ = x.saturating_mul(y);
            }
        };
    }

    // Small types: full input domain.
    nonzero_check_saturating_mul_small!(i8, NonZeroI8, nonzero_check_saturating_mul_for_i8);
    nonzero_check_saturating_mul_small!(i16, NonZeroI16, nonzero_check_saturating_mul_for_i16);
    nonzero_check_saturating_mul_small!(u8, NonZeroU8, nonzero_check_saturating_mul_for_u8);
    nonzero_check_saturating_mul_small!(u16, NonZeroU16, nonzero_check_saturating_mul_for_u16);

    // i32 intervals
    nonzero_check_saturating_mul_intervals!(
        i32,
        NonZeroI32,
        nonzero_check_saturating_mul_i32_small,
        NonZeroI32::new(-10i32).unwrap().into(),
        NonZeroI32::new(10i32).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        i32,
        NonZeroI32,
        nonzero_check_saturating_mul_i32_large_pos,
        NonZeroI32::new(i32::MAX - 1000i32).unwrap().into(),
        NonZeroI32::new(i32::MAX).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        i32,
        NonZeroI32,
        nonzero_check_saturating_mul_i32_large_neg,
        NonZeroI32::new(i32::MIN + 1).unwrap().into(),
        NonZeroI32::new(i32::MIN + 1000i32).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        i32,
        NonZeroI32,
        nonzero_check_saturating_mul_i32_edge_pos,
        NonZeroI32::new(i32::MAX / 2).unwrap().into(),
        NonZeroI32::new(i32::MAX).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        i32,
        NonZeroI32,
        nonzero_check_saturating_mul_i32_edge_neg,
        NonZeroI32::new(i32::MIN + 1).unwrap().into(),
        NonZeroI32::new(i32::MIN / 2).unwrap().into()
    );

    // i64 intervals
    nonzero_check_saturating_mul_intervals!(
        i64,
        NonZeroI64,
        nonzero_check_saturating_mul_i64_small,
        NonZeroI64::new(-10i64).unwrap().into(),
        NonZeroI64::new(10i64).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        i64,
        NonZeroI64,
        nonzero_check_saturating_mul_i64_large_pos,
        NonZeroI64::new(i64::MAX - 1000i64).unwrap().into(),
        NonZeroI64::new(i64::MAX).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        i64,
        NonZeroI64,
        nonzero_check_saturating_mul_i64_large_neg,
        NonZeroI64::new(i64::MIN + 1).unwrap().into(),
        NonZeroI64::new(i64::MIN + 1000i64).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        i64,
        NonZeroI64,
        nonzero_check_saturating_mul_i64_edge_pos,
        NonZeroI64::new(i64::MAX / 2).unwrap().into(),
        NonZeroI64::new(i64::MAX).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        i64,
        NonZeroI64,
        nonzero_check_saturating_mul_i64_edge_neg,
        NonZeroI64::new(i64::MIN + 1).unwrap().into(),
        NonZeroI64::new(i64::MIN / 2).unwrap().into()
    );

    // i128 intervals
    nonzero_check_saturating_mul_intervals!(
        i128,
        NonZeroI128,
        nonzero_check_saturating_mul_i128_small,
        NonZeroI128::new(-10i128).unwrap().into(),
        NonZeroI128::new(10i128).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        i128,
        NonZeroI128,
        nonzero_check_saturating_mul_i128_large_pos,
        NonZeroI128::new(i128::MAX - 1000i128).unwrap().into(),
        NonZeroI128::new(i128::MAX).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        i128,
        NonZeroI128,
        nonzero_check_saturating_mul_i128_large_neg,
        NonZeroI128::new(i128::MIN + 1).unwrap().into(),
        NonZeroI128::new(i128::MIN + 1000i128).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        i128,
        NonZeroI128,
        nonzero_check_saturating_mul_i128_edge_pos,
        NonZeroI128::new(i128::MAX / 2).unwrap().into(),
        NonZeroI128::new(i128::MAX).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        i128,
        NonZeroI128,
        nonzero_check_saturating_mul_i128_edge_neg,
        NonZeroI128::new(i128::MIN + 1).unwrap().into(),
        NonZeroI128::new(i128::MIN / 2).unwrap().into()
    );

    // isize intervals
    nonzero_check_saturating_mul_intervals!(
        isize,
        NonZeroIsize,
        nonzero_check_saturating_mul_isize_small,
        NonZeroIsize::new(-10isize).unwrap().into(),
        NonZeroIsize::new(10isize).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        isize,
        NonZeroIsize,
        nonzero_check_saturating_mul_isize_large_pos,
        NonZeroIsize::new(isize::MAX - 1000isize).unwrap().into(),
        NonZeroIsize::new(isize::MAX).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        isize,
        NonZeroIsize,
        nonzero_check_saturating_mul_isize_large_neg,
        NonZeroIsize::new(isize::MIN + 1).unwrap().into(),
        NonZeroIsize::new(isize::MIN + 1000isize).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        isize,
        NonZeroIsize,
        nonzero_check_saturating_mul_isize_edge_pos,
        NonZeroIsize::new(isize::MAX / 2).unwrap().into(),
        NonZeroIsize::new(isize::MAX).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        isize,
        NonZeroIsize,
        nonzero_check_saturating_mul_isize_edge_neg,
        NonZeroIsize::new(isize::MIN + 1).unwrap().into(),
        NonZeroIsize::new(isize::MIN / 2).unwrap().into()
    );

    // u32 intervals
    nonzero_check_saturating_mul_intervals!(
        u32,
        NonZeroU32,
        nonzero_check_saturating_mul_u32_small,
        NonZeroU32::new(1u32).unwrap().into(),
        NonZeroU32::new(10u32).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        u32,
        NonZeroU32,
        nonzero_check_saturating_mul_u32_large,
        NonZeroU32::new(u32::MAX - 1000u32).unwrap().into(),
        NonZeroU32::new(u32::MAX).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        u32,
        NonZeroU32,
        nonzero_check_saturating_mul_u32_edge,
        NonZeroU32::new(u32::MAX / 2).unwrap().into(),
        NonZeroU32::new(u32::MAX).unwrap().into()
    );

    // u64 intervals
    nonzero_check_saturating_mul_intervals!(
        u64,
        NonZeroU64,
        nonzero_check_saturating_mul_u64_small,
        NonZeroU64::new(1u64).unwrap().into(),
        NonZeroU64::new(10u64).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        u64,
        NonZeroU64,
        nonzero_check_saturating_mul_u64_large,
        NonZeroU64::new(u64::MAX - 1000u64).unwrap().into(),
        NonZeroU64::new(u64::MAX).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        u64,
        NonZeroU64,
        nonzero_check_saturating_mul_u64_edge,
        NonZeroU64::new(u64::MAX / 2).unwrap().into(),
        NonZeroU64::new(u64::MAX).unwrap().into()
    );

    // u128 intervals
    nonzero_check_saturating_mul_intervals!(
        u128,
        NonZeroU128,
        nonzero_check_saturating_mul_u128_small,
        NonZeroU128::new(1u128).unwrap().into(),
        NonZeroU128::new(10u128).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        u128,
        NonZeroU128,
        nonzero_check_saturating_mul_u128_large,
        NonZeroU128::new(u128::MAX - 1000u128).unwrap().into(),
        NonZeroU128::new(u128::MAX).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        u128,
        NonZeroU128,
        nonzero_check_saturating_mul_u128_edge,
        NonZeroU128::new(u128::MAX / 2).unwrap().into(),
        NonZeroU128::new(u128::MAX).unwrap().into()
    );

    // usize intervals
    nonzero_check_saturating_mul_intervals!(
        usize,
        NonZeroUsize,
        nonzero_check_saturating_mul_usize_small,
        NonZeroUsize::new(1usize).unwrap().into(),
        NonZeroUsize::new(10usize).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        usize,
        NonZeroUsize,
        nonzero_check_saturating_mul_usize_large,
        NonZeroUsize::new(usize::MAX - 1000usize).unwrap().into(),
        NonZeroUsize::new(usize::MAX).unwrap().into()
    );
    nonzero_check_saturating_mul_intervals!(
        usize,
        NonZeroUsize,
        nonzero_check_saturating_mul_usize_edge,
        NonZeroUsize::new(usize::MAX / 2).unwrap().into(),
        NonZeroUsize::new(usize::MAX).unwrap().into()
    );

    macro_rules! nonzero_check_add {
        ($t:ty, $nonzero_type:ty, $nonzero_check_unchecked_add_for:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::unchecked_add)]
            pub fn $nonzero_check_unchecked_add_for() {
                let x: $nonzero_type = kani::any();
                let y: $t = kani::any();

                unsafe {
                    x.unchecked_add(y);
                }
            }
        };
    }

    nonzero_check_add!(u8, core::num::NonZeroU8, nonzero_check_unchecked_add_for_u8);
    nonzero_check_add!(u16, core::num::NonZeroU16, nonzero_check_unchecked_add_for_u16);
    nonzero_check_add!(u32, core::num::NonZeroU32, nonzero_check_unchecked_add_for_u32);
    nonzero_check_add!(u64, core::num::NonZeroU64, nonzero_check_unchecked_add_for_u64);
    nonzero_check_add!(u128, core::num::NonZeroU128, nonzero_check_unchecked_add_for_u128);
    nonzero_check_add!(usize, core::num::NonZeroUsize, nonzero_check_unchecked_add_for_usize);

    // `checked_add` harnesses: verify the contract (`Some` iff no overflow, with
    // the exact sum, necessarily >= 1) and, with it, the internal
    // `new_unchecked`. Unsigned only; full input domain per width.
    macro_rules! nonzero_check_checked_add {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::checked_add)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let y: $t = kani::any();
                let _ = x.checked_add(y);
            }
        };
    }

    nonzero_check_checked_add!(u8, core::num::NonZeroU8, nonzero_check_checked_add_for_u8);
    nonzero_check_checked_add!(u16, core::num::NonZeroU16, nonzero_check_checked_add_for_u16);
    nonzero_check_checked_add!(u32, core::num::NonZeroU32, nonzero_check_checked_add_for_u32);
    nonzero_check_checked_add!(u64, core::num::NonZeroU64, nonzero_check_checked_add_for_u64);
    nonzero_check_checked_add!(u128, core::num::NonZeroU128, nonzero_check_checked_add_for_u128);
    nonzero_check_checked_add!(usize, core::num::NonZeroUsize, nonzero_check_checked_add_for_usize);

    // `saturating_add` harnesses: verify the contract (exact
    // `$Int::saturating_add` value, >= 1 in both the exact and saturated cases)
    // and, with it, the internal `new_unchecked`. Unsigned only; full input
    // domain per width.
    macro_rules! nonzero_check_saturating_add {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::saturating_add)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let y: $t = kani::any();
                let _ = x.saturating_add(y);
            }
        };
    }

    nonzero_check_saturating_add!(u8, core::num::NonZeroU8, nonzero_check_saturating_add_for_u8);
    nonzero_check_saturating_add!(u16, core::num::NonZeroU16, nonzero_check_saturating_add_for_u16);
    nonzero_check_saturating_add!(u32, core::num::NonZeroU32, nonzero_check_saturating_add_for_u32);
    nonzero_check_saturating_add!(u64, core::num::NonZeroU64, nonzero_check_saturating_add_for_u64);
    nonzero_check_saturating_add!(
        u128,
        core::num::NonZeroU128,
        nonzero_check_saturating_add_for_u128
    );
    nonzero_check_saturating_add!(
        usize,
        core::num::NonZeroUsize,
        nonzero_check_saturating_add_for_usize
    );

    // `checked_next_power_of_two` harnesses: verify the contract (`Some` iff the
    // next power of two fits, with the exact value, necessarily >= 1) and, with
    // it, the internal `new_unchecked`. Unsigned only; full nonzero domain per
    // width.
    macro_rules! nonzero_check_checked_next_power_of_two {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::checked_next_power_of_two)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.checked_next_power_of_two();
            }
        };
    }

    nonzero_check_checked_next_power_of_two!(
        u8,
        core::num::NonZeroU8,
        nonzero_check_checked_next_power_of_two_for_u8
    );
    nonzero_check_checked_next_power_of_two!(
        u16,
        core::num::NonZeroU16,
        nonzero_check_checked_next_power_of_two_for_u16
    );
    nonzero_check_checked_next_power_of_two!(
        u32,
        core::num::NonZeroU32,
        nonzero_check_checked_next_power_of_two_for_u32
    );
    nonzero_check_checked_next_power_of_two!(
        u64,
        core::num::NonZeroU64,
        nonzero_check_checked_next_power_of_two_for_u64
    );
    nonzero_check_checked_next_power_of_two!(
        u128,
        core::num::NonZeroU128,
        nonzero_check_checked_next_power_of_two_for_u128
    );
    nonzero_check_checked_next_power_of_two!(
        usize,
        core::num::NonZeroUsize,
        nonzero_check_checked_next_power_of_two_for_usize
    );

    // `count_ones` harnesses: a nonzero input has at least one set bit, so the
    // popcount is nonzero, discharging the internal `new_unchecked`. Full
    // nonzero domain per width.
    macro_rules! nonzero_check_count_ones {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::count_ones)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.count_ones();
            }
        };
    }

    nonzero_check_count_ones!(i8, core::num::NonZeroI8, nonzero_check_count_ones_for_i8);
    nonzero_check_count_ones!(i16, core::num::NonZeroI16, nonzero_check_count_ones_for_i16);
    nonzero_check_count_ones!(i32, core::num::NonZeroI32, nonzero_check_count_ones_for_i32);
    nonzero_check_count_ones!(i64, core::num::NonZeroI64, nonzero_check_count_ones_for_i64);
    nonzero_check_count_ones!(i128, core::num::NonZeroI128, nonzero_check_count_ones_for_i128);
    nonzero_check_count_ones!(isize, core::num::NonZeroIsize, nonzero_check_count_ones_for_isize);
    nonzero_check_count_ones!(u8, core::num::NonZeroU8, nonzero_check_count_ones_for_u8);
    nonzero_check_count_ones!(u16, core::num::NonZeroU16, nonzero_check_count_ones_for_u16);
    nonzero_check_count_ones!(u32, core::num::NonZeroU32, nonzero_check_count_ones_for_u32);
    nonzero_check_count_ones!(u64, core::num::NonZeroU64, nonzero_check_count_ones_for_u64);
    nonzero_check_count_ones!(u128, core::num::NonZeroU128, nonzero_check_count_ones_for_u128);
    nonzero_check_count_ones!(usize, core::num::NonZeroUsize, nonzero_check_count_ones_for_usize);

    // `swap_bytes` harnesses: a byte permutation keeps a nonzero value nonzero,
    // discharging the internal `new_unchecked`; the contract also pins the exact
    // value. Full nonzero domain per width.
    macro_rules! nonzero_check_swap_bytes {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::swap_bytes)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.swap_bytes();
            }
        };
    }

    nonzero_check_swap_bytes!(i8, core::num::NonZeroI8, nonzero_check_swap_bytes_for_i8);
    nonzero_check_swap_bytes!(i16, core::num::NonZeroI16, nonzero_check_swap_bytes_for_i16);
    nonzero_check_swap_bytes!(i32, core::num::NonZeroI32, nonzero_check_swap_bytes_for_i32);
    nonzero_check_swap_bytes!(i64, core::num::NonZeroI64, nonzero_check_swap_bytes_for_i64);
    nonzero_check_swap_bytes!(i128, core::num::NonZeroI128, nonzero_check_swap_bytes_for_i128);
    nonzero_check_swap_bytes!(isize, core::num::NonZeroIsize, nonzero_check_swap_bytes_for_isize);
    nonzero_check_swap_bytes!(u8, core::num::NonZeroU8, nonzero_check_swap_bytes_for_u8);
    nonzero_check_swap_bytes!(u16, core::num::NonZeroU16, nonzero_check_swap_bytes_for_u16);
    nonzero_check_swap_bytes!(u32, core::num::NonZeroU32, nonzero_check_swap_bytes_for_u32);
    nonzero_check_swap_bytes!(u64, core::num::NonZeroU64, nonzero_check_swap_bytes_for_u64);
    nonzero_check_swap_bytes!(u128, core::num::NonZeroU128, nonzero_check_swap_bytes_for_u128);
    nonzero_check_swap_bytes!(usize, core::num::NonZeroUsize, nonzero_check_swap_bytes_for_usize);

    // `reverse_bits` harnesses: a bit permutation keeps a nonzero value nonzero,
    // discharging the internal `new_unchecked`; the contract also pins the exact
    // value. Full nonzero domain per width.
    macro_rules! nonzero_check_reverse_bits {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::reverse_bits)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.reverse_bits();
            }
        };
    }

    nonzero_check_reverse_bits!(i8, core::num::NonZeroI8, nonzero_check_reverse_bits_for_i8);
    nonzero_check_reverse_bits!(i16, core::num::NonZeroI16, nonzero_check_reverse_bits_for_i16);
    nonzero_check_reverse_bits!(i32, core::num::NonZeroI32, nonzero_check_reverse_bits_for_i32);
    nonzero_check_reverse_bits!(i64, core::num::NonZeroI64, nonzero_check_reverse_bits_for_i64);
    nonzero_check_reverse_bits!(i128, core::num::NonZeroI128, nonzero_check_reverse_bits_for_i128);
    nonzero_check_reverse_bits!(
        isize,
        core::num::NonZeroIsize,
        nonzero_check_reverse_bits_for_isize
    );
    nonzero_check_reverse_bits!(u8, core::num::NonZeroU8, nonzero_check_reverse_bits_for_u8);
    nonzero_check_reverse_bits!(u16, core::num::NonZeroU16, nonzero_check_reverse_bits_for_u16);
    nonzero_check_reverse_bits!(u32, core::num::NonZeroU32, nonzero_check_reverse_bits_for_u32);
    nonzero_check_reverse_bits!(u64, core::num::NonZeroU64, nonzero_check_reverse_bits_for_u64);
    nonzero_check_reverse_bits!(u128, core::num::NonZeroU128, nonzero_check_reverse_bits_for_u128);
    nonzero_check_reverse_bits!(
        usize,
        core::num::NonZeroUsize,
        nonzero_check_reverse_bits_for_usize
    );

    // `rotate_left` harnesses: a rotation is a bit permutation, so nonzero stays
    // nonzero, discharging the internal `new_unchecked`; the `rotate_right`
    // round-trip pins correctness. Full nonzero domain per width; `n` ranges
    // over all of `u32` (rotation reduces it modulo the bit width).
    macro_rules! nonzero_check_rotate_left {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::rotate_left)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let n: u32 = kani::any();
                let _ = x.rotate_left(n);
            }
        };
    }

    nonzero_check_rotate_left!(i8, core::num::NonZeroI8, nonzero_check_rotate_left_for_i8);
    nonzero_check_rotate_left!(i16, core::num::NonZeroI16, nonzero_check_rotate_left_for_i16);
    nonzero_check_rotate_left!(i32, core::num::NonZeroI32, nonzero_check_rotate_left_for_i32);
    nonzero_check_rotate_left!(i64, core::num::NonZeroI64, nonzero_check_rotate_left_for_i64);
    nonzero_check_rotate_left!(i128, core::num::NonZeroI128, nonzero_check_rotate_left_for_i128);
    nonzero_check_rotate_left!(isize, core::num::NonZeroIsize, nonzero_check_rotate_left_for_isize);
    nonzero_check_rotate_left!(u8, core::num::NonZeroU8, nonzero_check_rotate_left_for_u8);
    nonzero_check_rotate_left!(u16, core::num::NonZeroU16, nonzero_check_rotate_left_for_u16);
    nonzero_check_rotate_left!(u32, core::num::NonZeroU32, nonzero_check_rotate_left_for_u32);
    nonzero_check_rotate_left!(u64, core::num::NonZeroU64, nonzero_check_rotate_left_for_u64);
    nonzero_check_rotate_left!(u128, core::num::NonZeroU128, nonzero_check_rotate_left_for_u128);
    nonzero_check_rotate_left!(usize, core::num::NonZeroUsize, nonzero_check_rotate_left_for_usize);

    // `rotate_right` harnesses: mirror of `rotate_left` above, with the
    // `rotate_left` round-trip pinning correctness. Full nonzero domain per
    // width; `n` ranges over all of `u32`.
    macro_rules! nonzero_check_rotate_right {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::rotate_right)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let n: u32 = kani::any();
                let _ = x.rotate_right(n);
            }
        };
    }

    nonzero_check_rotate_right!(i8, core::num::NonZeroI8, nonzero_check_rotate_right_for_i8);
    nonzero_check_rotate_right!(i16, core::num::NonZeroI16, nonzero_check_rotate_right_for_i16);
    nonzero_check_rotate_right!(i32, core::num::NonZeroI32, nonzero_check_rotate_right_for_i32);
    nonzero_check_rotate_right!(i64, core::num::NonZeroI64, nonzero_check_rotate_right_for_i64);
    nonzero_check_rotate_right!(i128, core::num::NonZeroI128, nonzero_check_rotate_right_for_i128);
    nonzero_check_rotate_right!(
        isize,
        core::num::NonZeroIsize,
        nonzero_check_rotate_right_for_isize
    );
    nonzero_check_rotate_right!(u8, core::num::NonZeroU8, nonzero_check_rotate_right_for_u8);
    nonzero_check_rotate_right!(u16, core::num::NonZeroU16, nonzero_check_rotate_right_for_u16);
    nonzero_check_rotate_right!(u32, core::num::NonZeroU32, nonzero_check_rotate_right_for_u32);
    nonzero_check_rotate_right!(u64, core::num::NonZeroU64, nonzero_check_rotate_right_for_u64);
    nonzero_check_rotate_right!(u128, core::num::NonZeroU128, nonzero_check_rotate_right_for_u128);
    nonzero_check_rotate_right!(
        usize,
        core::num::NonZeroUsize,
        nonzero_check_rotate_right_for_usize
    );

    // `from_be` harnesses: identity or byte permutation depending on target
    // endianness — either way nonzero stays nonzero, discharging the internal
    // `new_unchecked`; the contract also pins the exact value. Full nonzero
    // domain per width.
    macro_rules! nonzero_check_from_be {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::from_be)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = <$nonzero_type>::from_be(x);
            }
        };
    }

    nonzero_check_from_be!(i8, core::num::NonZeroI8, nonzero_check_from_be_for_i8);
    nonzero_check_from_be!(i16, core::num::NonZeroI16, nonzero_check_from_be_for_i16);
    nonzero_check_from_be!(i32, core::num::NonZeroI32, nonzero_check_from_be_for_i32);
    nonzero_check_from_be!(i64, core::num::NonZeroI64, nonzero_check_from_be_for_i64);
    nonzero_check_from_be!(i128, core::num::NonZeroI128, nonzero_check_from_be_for_i128);
    nonzero_check_from_be!(isize, core::num::NonZeroIsize, nonzero_check_from_be_for_isize);
    nonzero_check_from_be!(u8, core::num::NonZeroU8, nonzero_check_from_be_for_u8);
    nonzero_check_from_be!(u16, core::num::NonZeroU16, nonzero_check_from_be_for_u16);
    nonzero_check_from_be!(u32, core::num::NonZeroU32, nonzero_check_from_be_for_u32);
    nonzero_check_from_be!(u64, core::num::NonZeroU64, nonzero_check_from_be_for_u64);
    nonzero_check_from_be!(u128, core::num::NonZeroU128, nonzero_check_from_be_for_u128);
    nonzero_check_from_be!(usize, core::num::NonZeroUsize, nonzero_check_from_be_for_usize);

    // `from_le` harnesses: identity or byte permutation depending on target
    // endianness — either way nonzero stays nonzero, discharging the internal
    // `new_unchecked`; the contract also pins the exact value. Full nonzero
    // domain per width.
    macro_rules! nonzero_check_from_le {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::from_le)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = <$nonzero_type>::from_le(x);
            }
        };
    }

    nonzero_check_from_le!(i8, core::num::NonZeroI8, nonzero_check_from_le_for_i8);
    nonzero_check_from_le!(i16, core::num::NonZeroI16, nonzero_check_from_le_for_i16);
    nonzero_check_from_le!(i32, core::num::NonZeroI32, nonzero_check_from_le_for_i32);
    nonzero_check_from_le!(i64, core::num::NonZeroI64, nonzero_check_from_le_for_i64);
    nonzero_check_from_le!(i128, core::num::NonZeroI128, nonzero_check_from_le_for_i128);
    nonzero_check_from_le!(isize, core::num::NonZeroIsize, nonzero_check_from_le_for_isize);
    nonzero_check_from_le!(u8, core::num::NonZeroU8, nonzero_check_from_le_for_u8);
    nonzero_check_from_le!(u16, core::num::NonZeroU16, nonzero_check_from_le_for_u16);
    nonzero_check_from_le!(u32, core::num::NonZeroU32, nonzero_check_from_le_for_u32);
    nonzero_check_from_le!(u64, core::num::NonZeroU64, nonzero_check_from_le_for_u64);
    nonzero_check_from_le!(u128, core::num::NonZeroU128, nonzero_check_from_le_for_u128);
    nonzero_check_from_le!(usize, core::num::NonZeroUsize, nonzero_check_from_le_for_usize);

    // `to_be` harnesses: identity or byte permutation depending on target
    // endianness — either way nonzero stays nonzero, discharging the internal
    // `new_unchecked`; the contract also pins the exact value. Full nonzero
    // domain per width.
    macro_rules! nonzero_check_to_be {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::to_be)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.to_be();
            }
        };
    }

    nonzero_check_to_be!(i8, core::num::NonZeroI8, nonzero_check_to_be_for_i8);
    nonzero_check_to_be!(i16, core::num::NonZeroI16, nonzero_check_to_be_for_i16);
    nonzero_check_to_be!(i32, core::num::NonZeroI32, nonzero_check_to_be_for_i32);
    nonzero_check_to_be!(i64, core::num::NonZeroI64, nonzero_check_to_be_for_i64);
    nonzero_check_to_be!(i128, core::num::NonZeroI128, nonzero_check_to_be_for_i128);
    nonzero_check_to_be!(isize, core::num::NonZeroIsize, nonzero_check_to_be_for_isize);
    nonzero_check_to_be!(u8, core::num::NonZeroU8, nonzero_check_to_be_for_u8);
    nonzero_check_to_be!(u16, core::num::NonZeroU16, nonzero_check_to_be_for_u16);
    nonzero_check_to_be!(u32, core::num::NonZeroU32, nonzero_check_to_be_for_u32);
    nonzero_check_to_be!(u64, core::num::NonZeroU64, nonzero_check_to_be_for_u64);
    nonzero_check_to_be!(u128, core::num::NonZeroU128, nonzero_check_to_be_for_u128);
    nonzero_check_to_be!(usize, core::num::NonZeroUsize, nonzero_check_to_be_for_usize);

    // `to_le` harnesses: identity or byte permutation depending on target
    // endianness — either way nonzero stays nonzero, discharging the internal
    // `new_unchecked`; the contract also pins the exact value. Full nonzero
    // domain per width.
    macro_rules! nonzero_check_to_le {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::to_le)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.to_le();
            }
        };
    }

    nonzero_check_to_le!(i8, core::num::NonZeroI8, nonzero_check_to_le_for_i8);
    nonzero_check_to_le!(i16, core::num::NonZeroI16, nonzero_check_to_le_for_i16);
    nonzero_check_to_le!(i32, core::num::NonZeroI32, nonzero_check_to_le_for_i32);
    nonzero_check_to_le!(i64, core::num::NonZeroI64, nonzero_check_to_le_for_i64);
    nonzero_check_to_le!(i128, core::num::NonZeroI128, nonzero_check_to_le_for_i128);
    nonzero_check_to_le!(isize, core::num::NonZeroIsize, nonzero_check_to_le_for_isize);
    nonzero_check_to_le!(u8, core::num::NonZeroU8, nonzero_check_to_le_for_u8);
    nonzero_check_to_le!(u16, core::num::NonZeroU16, nonzero_check_to_le_for_u16);
    nonzero_check_to_le!(u32, core::num::NonZeroU32, nonzero_check_to_le_for_u32);
    nonzero_check_to_le!(u64, core::num::NonZeroU64, nonzero_check_to_le_for_u64);
    nonzero_check_to_le!(u128, core::num::NonZeroU128, nonzero_check_to_le_for_u128);
    nonzero_check_to_le!(usize, core::num::NonZeroUsize, nonzero_check_to_le_for_usize);

    // `BitOr` harnesses (all three impls): OR-ing with a `NonZero` operand keeps
    // at least one bit set, so the result is nonzero, discharging the internal
    // `new_unchecked`; assertions pin nonzero-ness and the exact value. `bitor`
    // is generic over `ZeroablePrimitive`, so — like `max`/`min`/`clamp` above —
    // plain `#[kani::proof]` harnesses are used instead of a contract. Full
    // nonzero domain per width.

    // `impl BitOr for NonZero<T>`: `NonZero | NonZero -> NonZero`.
    macro_rules! nonzero_check_bitor_both_nonzero {
        ($nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof]
            pub fn $harness_name() {
                let a: $nonzero_type = kani::any();
                let b: $nonzero_type = kani::any();
                let result = a | b;
                assert!(result.get() == (a.get() | b.get()));
                assert!(result.get() != 0);
            }
        };
    }

    nonzero_check_bitor_both_nonzero!(core::num::NonZeroI8, nonzero_check_bitor_both_nonzero_i8);
    nonzero_check_bitor_both_nonzero!(core::num::NonZeroI16, nonzero_check_bitor_both_nonzero_i16);
    nonzero_check_bitor_both_nonzero!(core::num::NonZeroI32, nonzero_check_bitor_both_nonzero_i32);
    nonzero_check_bitor_both_nonzero!(core::num::NonZeroI64, nonzero_check_bitor_both_nonzero_i64);
    nonzero_check_bitor_both_nonzero!(
        core::num::NonZeroI128,
        nonzero_check_bitor_both_nonzero_i128
    );
    nonzero_check_bitor_both_nonzero!(
        core::num::NonZeroIsize,
        nonzero_check_bitor_both_nonzero_isize
    );
    nonzero_check_bitor_both_nonzero!(core::num::NonZeroU8, nonzero_check_bitor_both_nonzero_u8);
    nonzero_check_bitor_both_nonzero!(core::num::NonZeroU16, nonzero_check_bitor_both_nonzero_u16);
    nonzero_check_bitor_both_nonzero!(core::num::NonZeroU32, nonzero_check_bitor_both_nonzero_u32);
    nonzero_check_bitor_both_nonzero!(core::num::NonZeroU64, nonzero_check_bitor_both_nonzero_u64);
    nonzero_check_bitor_both_nonzero!(
        core::num::NonZeroU128,
        nonzero_check_bitor_both_nonzero_u128
    );
    nonzero_check_bitor_both_nonzero!(
        core::num::NonZeroUsize,
        nonzero_check_bitor_both_nonzero_usize
    );

    // `impl BitOr<T> for NonZero<T>`: `NonZero | primitive -> NonZero`.
    macro_rules! nonzero_check_bitor_rhs_primitive {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof]
            pub fn $harness_name() {
                let a: $nonzero_type = kani::any();
                let b: $t = kani::any();
                let result = a | b;
                assert!(result.get() == (a.get() | b));
                assert!(result.get() != 0);
            }
        };
    }

    nonzero_check_bitor_rhs_primitive!(
        i8,
        core::num::NonZeroI8,
        nonzero_check_bitor_rhs_primitive_i8
    );
    nonzero_check_bitor_rhs_primitive!(
        i16,
        core::num::NonZeroI16,
        nonzero_check_bitor_rhs_primitive_i16
    );
    nonzero_check_bitor_rhs_primitive!(
        i32,
        core::num::NonZeroI32,
        nonzero_check_bitor_rhs_primitive_i32
    );
    nonzero_check_bitor_rhs_primitive!(
        i64,
        core::num::NonZeroI64,
        nonzero_check_bitor_rhs_primitive_i64
    );
    nonzero_check_bitor_rhs_primitive!(
        i128,
        core::num::NonZeroI128,
        nonzero_check_bitor_rhs_primitive_i128
    );
    nonzero_check_bitor_rhs_primitive!(
        isize,
        core::num::NonZeroIsize,
        nonzero_check_bitor_rhs_primitive_isize
    );
    nonzero_check_bitor_rhs_primitive!(
        u8,
        core::num::NonZeroU8,
        nonzero_check_bitor_rhs_primitive_u8
    );
    nonzero_check_bitor_rhs_primitive!(
        u16,
        core::num::NonZeroU16,
        nonzero_check_bitor_rhs_primitive_u16
    );
    nonzero_check_bitor_rhs_primitive!(
        u32,
        core::num::NonZeroU32,
        nonzero_check_bitor_rhs_primitive_u32
    );
    nonzero_check_bitor_rhs_primitive!(
        u64,
        core::num::NonZeroU64,
        nonzero_check_bitor_rhs_primitive_u64
    );
    nonzero_check_bitor_rhs_primitive!(
        u128,
        core::num::NonZeroU128,
        nonzero_check_bitor_rhs_primitive_u128
    );
    nonzero_check_bitor_rhs_primitive!(
        usize,
        core::num::NonZeroUsize,
        nonzero_check_bitor_rhs_primitive_usize
    );

    // `impl BitOr<NonZero<T>> for T`: `primitive | NonZero -> NonZero`.
    macro_rules! nonzero_check_bitor_lhs_primitive {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof]
            pub fn $harness_name() {
                let a: $t = kani::any();
                let b: $nonzero_type = kani::any();
                let result = a | b;
                assert!(result.get() == (a | b.get()));
                assert!(result.get() != 0);
            }
        };
    }

    nonzero_check_bitor_lhs_primitive!(
        i8,
        core::num::NonZeroI8,
        nonzero_check_bitor_lhs_primitive_i8
    );
    nonzero_check_bitor_lhs_primitive!(
        i16,
        core::num::NonZeroI16,
        nonzero_check_bitor_lhs_primitive_i16
    );
    nonzero_check_bitor_lhs_primitive!(
        i32,
        core::num::NonZeroI32,
        nonzero_check_bitor_lhs_primitive_i32
    );
    nonzero_check_bitor_lhs_primitive!(
        i64,
        core::num::NonZeroI64,
        nonzero_check_bitor_lhs_primitive_i64
    );
    nonzero_check_bitor_lhs_primitive!(
        i128,
        core::num::NonZeroI128,
        nonzero_check_bitor_lhs_primitive_i128
    );
    nonzero_check_bitor_lhs_primitive!(
        isize,
        core::num::NonZeroIsize,
        nonzero_check_bitor_lhs_primitive_isize
    );
    nonzero_check_bitor_lhs_primitive!(
        u8,
        core::num::NonZeroU8,
        nonzero_check_bitor_lhs_primitive_u8
    );
    nonzero_check_bitor_lhs_primitive!(
        u16,
        core::num::NonZeroU16,
        nonzero_check_bitor_lhs_primitive_u16
    );
    nonzero_check_bitor_lhs_primitive!(
        u32,
        core::num::NonZeroU32,
        nonzero_check_bitor_lhs_primitive_u32
    );
    nonzero_check_bitor_lhs_primitive!(
        u64,
        core::num::NonZeroU64,
        nonzero_check_bitor_lhs_primitive_u64
    );
    nonzero_check_bitor_lhs_primitive!(
        u128,
        core::num::NonZeroU128,
        nonzero_check_bitor_lhs_primitive_u128
    );
    nonzero_check_bitor_lhs_primitive!(
        usize,
        core::num::NonZeroUsize,
        nonzero_check_bitor_lhs_primitive_usize
    );

    // `neg` harnesses (the `Neg` impl, signed only): negating nonzero is
    // nonzero, discharging the internal `new_unchecked`. As a trait method it
    // gets plain harnesses instead of a contract. Paired value/panic harnesses
    // split the domain (`abs`/`clamp` pattern): the value harness covers all
    // non-`MIN` inputs and asserts nonzero-ness plus `result == -x`; the
    // `should_panic` harness proves `MIN` panics (overflow checks are always on
    // under Kani).
    macro_rules! nonzero_check_neg {
        ($t:ty, $nonzero_type:ty, $harness_name:ident, $panic_harness_name:ident) => {
            #[kani::proof]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                kani::assume(x.get() != <$t>::MIN);
                kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
                let result = -x;
                assert!(result.get() == -x.get());
                assert!(result.get() != 0);
            }

            #[kani::proof]
            #[kani::should_panic]
            pub fn $panic_harness_name() {
                let x: $nonzero_type = kani::any();
                kani::assume(x.get() == <$t>::MIN);
                kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
                let _ = -x;
            }
        };
    }

    nonzero_check_neg!(
        i8,
        core::num::NonZeroI8,
        nonzero_check_neg_i8,
        nonzero_check_neg_min_panics_i8
    );
    nonzero_check_neg!(
        i16,
        core::num::NonZeroI16,
        nonzero_check_neg_i16,
        nonzero_check_neg_min_panics_i16
    );
    nonzero_check_neg!(
        i32,
        core::num::NonZeroI32,
        nonzero_check_neg_i32,
        nonzero_check_neg_min_panics_i32
    );
    nonzero_check_neg!(
        i64,
        core::num::NonZeroI64,
        nonzero_check_neg_i64,
        nonzero_check_neg_min_panics_i64
    );
    nonzero_check_neg!(
        i128,
        core::num::NonZeroI128,
        nonzero_check_neg_i128,
        nonzero_check_neg_min_panics_i128
    );
    nonzero_check_neg!(
        isize,
        core::num::NonZeroIsize,
        nonzero_check_neg_isize,
        nonzero_check_neg_min_panics_isize
    );

    // `checked_neg` harnesses: verify the contract (`None` iff `self == MIN`,
    // else the exact negation) and, with it, the internal `new_unchecked`.
    // Signed only; full nonzero domain per width, no input assumption (the
    // overflow case returns `None`).
    macro_rules! nonzero_check_checked_neg {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::checked_neg)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.checked_neg();
            }
        };
    }

    nonzero_check_checked_neg!(i8, core::num::NonZeroI8, nonzero_check_checked_neg_i8);
    nonzero_check_checked_neg!(i16, core::num::NonZeroI16, nonzero_check_checked_neg_i16);
    nonzero_check_checked_neg!(i32, core::num::NonZeroI32, nonzero_check_checked_neg_i32);
    nonzero_check_checked_neg!(i64, core::num::NonZeroI64, nonzero_check_checked_neg_i64);
    nonzero_check_checked_neg!(i128, core::num::NonZeroI128, nonzero_check_checked_neg_i128);
    nonzero_check_checked_neg!(isize, core::num::NonZeroIsize, nonzero_check_checked_neg_isize);

    // `overflowing_neg` harnesses: verify the contract (flag iff `self == MIN`,
    // value == `wrapping_neg`) and, with it, the internal `new_unchecked`.
    // Signed only; full nonzero domain per width, no input assumption (the
    // overflow case wraps).
    macro_rules! nonzero_check_overflowing_neg {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::overflowing_neg)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.overflowing_neg();
            }
        };
    }

    nonzero_check_overflowing_neg!(i8, core::num::NonZeroI8, nonzero_check_overflowing_neg_i8);
    nonzero_check_overflowing_neg!(i16, core::num::NonZeroI16, nonzero_check_overflowing_neg_i16);
    nonzero_check_overflowing_neg!(i32, core::num::NonZeroI32, nonzero_check_overflowing_neg_i32);
    nonzero_check_overflowing_neg!(i64, core::num::NonZeroI64, nonzero_check_overflowing_neg_i64);
    nonzero_check_overflowing_neg!(
        i128,
        core::num::NonZeroI128,
        nonzero_check_overflowing_neg_i128
    );
    nonzero_check_overflowing_neg!(
        isize,
        core::num::NonZeroIsize,
        nonzero_check_overflowing_neg_isize
    );

    // `wrapping_neg` harnesses: verify the contract (value == `wrapping_neg`)
    // and, with it, the internal `new_unchecked`. Signed only; full nonzero
    // domain per width, no input assumption (the overflow case wraps).
    macro_rules! nonzero_check_wrapping_neg {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::wrapping_neg)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.wrapping_neg();
            }
        };
    }

    nonzero_check_wrapping_neg!(i8, core::num::NonZeroI8, nonzero_check_wrapping_neg_i8);
    nonzero_check_wrapping_neg!(i16, core::num::NonZeroI16, nonzero_check_wrapping_neg_i16);
    nonzero_check_wrapping_neg!(i32, core::num::NonZeroI32, nonzero_check_wrapping_neg_i32);
    nonzero_check_wrapping_neg!(i64, core::num::NonZeroI64, nonzero_check_wrapping_neg_i64);
    nonzero_check_wrapping_neg!(i128, core::num::NonZeroI128, nonzero_check_wrapping_neg_i128);
    nonzero_check_wrapping_neg!(isize, core::num::NonZeroIsize, nonzero_check_wrapping_neg_isize);

    // `abs` harnesses (signed only): paired value/panic harnesses split the
    // domain (`clamp`/`clamp_panic` pattern) since `abs` is total but panics on
    // `MIN` under overflow checks (always on under Kani). The value harness
    // covers all non-`MIN` inputs against the contract; the `should_panic`
    // harness proves the `MIN` panic.
    macro_rules! nonzero_check_abs {
        ($t:ty, $nonzero_type:ty, $harness_name:ident, $panic_harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::abs)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                kani::assume(x.get() != <$t>::MIN);
                kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
                let _ = x.abs();
            }

            #[kani::proof]
            #[kani::should_panic]
            pub fn $panic_harness_name() {
                let x: $nonzero_type = kani::any();
                kani::assume(x.get() == <$t>::MIN);
                kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
                let _ = x.abs();
            }
        };
    }

    nonzero_check_abs!(
        i8,
        core::num::NonZeroI8,
        nonzero_check_abs_i8,
        nonzero_check_abs_min_panics_i8
    );
    nonzero_check_abs!(
        i16,
        core::num::NonZeroI16,
        nonzero_check_abs_i16,
        nonzero_check_abs_min_panics_i16
    );
    nonzero_check_abs!(
        i32,
        core::num::NonZeroI32,
        nonzero_check_abs_i32,
        nonzero_check_abs_min_panics_i32
    );
    nonzero_check_abs!(
        i64,
        core::num::NonZeroI64,
        nonzero_check_abs_i64,
        nonzero_check_abs_min_panics_i64
    );
    nonzero_check_abs!(
        i128,
        core::num::NonZeroI128,
        nonzero_check_abs_i128,
        nonzero_check_abs_min_panics_i128
    );
    nonzero_check_abs!(
        isize,
        core::num::NonZeroIsize,
        nonzero_check_abs_isize,
        nonzero_check_abs_min_panics_isize
    );

    // `checked_abs` harnesses: verify the contract (`None` iff `self == MIN`,
    // else the exact absolute value) and, with it, the internal `new_unchecked`.
    // Signed only; full nonzero domain per width, no input assumption (the
    // overflow case returns `None`).
    macro_rules! nonzero_check_checked_abs {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::checked_abs)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.checked_abs();
            }
        };
    }

    nonzero_check_checked_abs!(i8, core::num::NonZeroI8, nonzero_check_checked_abs_i8);
    nonzero_check_checked_abs!(i16, core::num::NonZeroI16, nonzero_check_checked_abs_i16);
    nonzero_check_checked_abs!(i32, core::num::NonZeroI32, nonzero_check_checked_abs_i32);
    nonzero_check_checked_abs!(i64, core::num::NonZeroI64, nonzero_check_checked_abs_i64);
    nonzero_check_checked_abs!(i128, core::num::NonZeroI128, nonzero_check_checked_abs_i128);
    nonzero_check_checked_abs!(isize, core::num::NonZeroIsize, nonzero_check_checked_abs_isize);

    // `overflowing_abs` harnesses: verify the contract (flag iff `self == MIN`,
    // value == `wrapping_abs`) and, with it, the internal `new_unchecked`.
    // Signed only; full nonzero domain per width, no input assumption (the
    // overflow case wraps and flags).
    macro_rules! nonzero_check_overflowing_abs {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::overflowing_abs)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.overflowing_abs();
            }
        };
    }

    nonzero_check_overflowing_abs!(i8, core::num::NonZeroI8, nonzero_check_overflowing_abs_i8);
    nonzero_check_overflowing_abs!(i16, core::num::NonZeroI16, nonzero_check_overflowing_abs_i16);
    nonzero_check_overflowing_abs!(i32, core::num::NonZeroI32, nonzero_check_overflowing_abs_i32);
    nonzero_check_overflowing_abs!(i64, core::num::NonZeroI64, nonzero_check_overflowing_abs_i64);
    nonzero_check_overflowing_abs!(
        i128,
        core::num::NonZeroI128,
        nonzero_check_overflowing_abs_i128
    );
    nonzero_check_overflowing_abs!(
        isize,
        core::num::NonZeroIsize,
        nonzero_check_overflowing_abs_isize
    );

    // `saturating_abs` harnesses: verify the contract (exact value, strictly
    // positive) and, with it, the internal `new_unchecked`. Signed only; full
    // nonzero domain per width, no input assumption (the overflow case clamps to
    // `MAX`).
    macro_rules! nonzero_check_saturating_abs {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::saturating_abs)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.saturating_abs();
            }
        };
    }

    nonzero_check_saturating_abs!(i8, core::num::NonZeroI8, nonzero_check_saturating_abs_i8);
    nonzero_check_saturating_abs!(i16, core::num::NonZeroI16, nonzero_check_saturating_abs_i16);
    nonzero_check_saturating_abs!(i32, core::num::NonZeroI32, nonzero_check_saturating_abs_i32);
    nonzero_check_saturating_abs!(i64, core::num::NonZeroI64, nonzero_check_saturating_abs_i64);
    nonzero_check_saturating_abs!(i128, core::num::NonZeroI128, nonzero_check_saturating_abs_i128);
    nonzero_check_saturating_abs!(
        isize,
        core::num::NonZeroIsize,
        nonzero_check_saturating_abs_isize
    );

    // `wrapping_abs` harnesses: verify the contract (value == `wrapping_abs`)
    // and, with it, the internal `new_unchecked`. Signed only; full nonzero
    // domain per width, no input assumption (the overflow case wraps).
    macro_rules! nonzero_check_wrapping_abs {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::wrapping_abs)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.wrapping_abs();
            }
        };
    }

    nonzero_check_wrapping_abs!(i8, core::num::NonZeroI8, nonzero_check_wrapping_abs_i8);
    nonzero_check_wrapping_abs!(i16, core::num::NonZeroI16, nonzero_check_wrapping_abs_i16);
    nonzero_check_wrapping_abs!(i32, core::num::NonZeroI32, nonzero_check_wrapping_abs_i32);
    nonzero_check_wrapping_abs!(i64, core::num::NonZeroI64, nonzero_check_wrapping_abs_i64);
    nonzero_check_wrapping_abs!(i128, core::num::NonZeroI128, nonzero_check_wrapping_abs_i128);
    nonzero_check_wrapping_abs!(isize, core::num::NonZeroIsize, nonzero_check_wrapping_abs_isize);

    // `unsigned_abs` harnesses: verify the contract (exact magnitude, strictly
    // positive) and, with it, the internal `new_unchecked`. Signed input, full
    // nonzero domain per width; never overflows (`MIN`'s magnitude fits the
    // unsigned target).
    macro_rules! nonzero_check_unsigned_abs {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::unsigned_abs)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.unsigned_abs();
            }
        };
    }

    nonzero_check_unsigned_abs!(i8, core::num::NonZeroI8, nonzero_check_unsigned_abs_i8);
    nonzero_check_unsigned_abs!(i16, core::num::NonZeroI16, nonzero_check_unsigned_abs_i16);
    nonzero_check_unsigned_abs!(i32, core::num::NonZeroI32, nonzero_check_unsigned_abs_i32);
    nonzero_check_unsigned_abs!(i64, core::num::NonZeroI64, nonzero_check_unsigned_abs_i64);
    nonzero_check_unsigned_abs!(i128, core::num::NonZeroI128, nonzero_check_unsigned_abs_i128);
    nonzero_check_unsigned_abs!(isize, core::num::NonZeroIsize, nonzero_check_unsigned_abs_isize);

    // `midpoint` harnesses: verify the contract (exact value; the average of two
    // values >= 1 is >= 1, and the underlying `midpoint` cannot overflow) and,
    // with it, the internal `new_unchecked`. Unsigned only; both operands range
    // over the full nonzero domain per width.
    macro_rules! nonzero_check_midpoint {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::midpoint)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let y: $nonzero_type = kani::any();
                let _ = x.midpoint(y);
            }
        };
    }

    nonzero_check_midpoint!(u8, core::num::NonZeroU8, nonzero_check_midpoint_u8);
    nonzero_check_midpoint!(u16, core::num::NonZeroU16, nonzero_check_midpoint_u16);
    nonzero_check_midpoint!(u32, core::num::NonZeroU32, nonzero_check_midpoint_u32);
    nonzero_check_midpoint!(u64, core::num::NonZeroU64, nonzero_check_midpoint_u64);
    nonzero_check_midpoint!(u128, core::num::NonZeroU128, nonzero_check_midpoint_u128);
    nonzero_check_midpoint!(usize, core::num::NonZeroUsize, nonzero_check_midpoint_usize);

    // `isqrt` harnesses: verify the contract (exact root; `isqrt(x >= 1) >= 1`)
    // and, with it, the internal `new_unchecked`. u8/u16/u32 get the full
    // nonzero domain. For u64/usize/u128 the staged `int_sqrt` reduction is
    // multiplication-heavy and CBMC cannot discharge full-width multiplication,
    // so those widths use value intervals: near 1, the root's half-width
    // transition band (2^32 / 2^64), and near `MAX`.
    //
    // KNOWN VERIFICATION GAP (u64/usize/u128): the contract — including the
    // exact-value clause — is machine-checked only within these intervals.
    // Monotonicity of `isqrt` is an informal (unchecked) argument that
    // nonzero-ness extends to the uncovered bands; it says nothing about the
    // exact-value clause. Closing the gap needs a tractable full-width
    // multiplication encoding or a functional invariant for the Newton loop.
    macro_rules! nonzero_check_isqrt {
        ($t:ty, $nonzero_type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract(NonZero::<$t>::isqrt)]
            pub fn $harness_name() {
                let x: $nonzero_type = kani::any();
                let _ = x.isqrt();
            }
        };
    }

    nonzero_check_isqrt!(u8, core::num::NonZeroU8, nonzero_check_isqrt_u8);
    nonzero_check_isqrt!(u16, core::num::NonZeroU16, nonzero_check_isqrt_u16);
    nonzero_check_isqrt!(u32, core::num::NonZeroU32, nonzero_check_isqrt_u32);

    // Interval-bounded harnesses for the wide widths (see note above). `$min`
    // and `$max` bound the underlying integer; `kani::assume` fixes the input's
    // high bits so CBMC can simplify the staged multiplications.
    macro_rules! nonzero_check_isqrt_interval {
        ($t:ty, $nonzero_type:ty, $harness_name:ident, $min:expr, $max:expr) => {
            #[kani::proof_for_contract(NonZero::<$t>::isqrt)]
            pub fn $harness_name() {
                let v = kani::any::<$t>();
                // Vacuity guard: inverted endpoints would make the assume
                // unsatisfiable; assert before assuming so it fails loudly.
                let (__ival_min, __ival_max): ($t, $t) = ($min, $max);
                assert!(__ival_min <= __ival_max, "interval endpoints inverted");
                kani::assume(v >= $min && v <= $max);
                kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
                let x = <$nonzero_type>::new(v).unwrap();
                let _ = x.isqrt();
            }
        };
    }

    // u64: small magnitudes (roots in [1, 0xFFFF]), the 2^32 half-width
    // transition band (roots crossing 0xFFFF_FFFF), and near-MAX magnitudes.
    nonzero_check_isqrt_interval!(
        u64,
        core::num::NonZeroU64,
        nonzero_check_isqrt_u64_small,
        1u64,
        0xFFFFu64
    );
    nonzero_check_isqrt_interval!(
        u64,
        core::num::NonZeroU64,
        nonzero_check_isqrt_u64_mid,
        (1u64 << 32) - 0xFFFFu64,
        (1u64 << 32) + 0xFFFFu64
    );
    nonzero_check_isqrt_interval!(
        u64,
        core::num::NonZeroU64,
        nonzero_check_isqrt_u64_large,
        u64::MAX - 0xFFFFu64,
        u64::MAX
    );

    // usize mirrors u64 on this 64-bit target.
    nonzero_check_isqrt_interval!(
        usize,
        core::num::NonZeroUsize,
        nonzero_check_isqrt_usize_small,
        1usize,
        0xFFFFusize
    );
    nonzero_check_isqrt_interval!(
        usize,
        core::num::NonZeroUsize,
        nonzero_check_isqrt_usize_mid,
        (1usize << 32) - 0xFFFFusize,
        (1usize << 32) + 0xFFFFusize
    );
    nonzero_check_isqrt_interval!(
        usize,
        core::num::NonZeroUsize,
        nonzero_check_isqrt_usize_large,
        usize::MAX - 0xFFFFusize,
        usize::MAX
    );

    // u128: same interval strategy at the widest type, with the transition
    // band at 2^64.
    nonzero_check_isqrt_interval!(
        u128,
        core::num::NonZeroU128,
        nonzero_check_isqrt_u128_small,
        1u128,
        0xFFFFu128
    );
    nonzero_check_isqrt_interval!(
        u128,
        core::num::NonZeroU128,
        nonzero_check_isqrt_u128_mid,
        (1u128 << 64) - 0xFFFFu128,
        (1u128 << 64) + 0xFFFFu128
    );
    nonzero_check_isqrt_interval!(
        u128,
        core::num::NonZeroU128,
        nonzero_check_isqrt_u128_large,
        u128::MAX - 0xFFFFu128,
        u128::MAX
    );
}
