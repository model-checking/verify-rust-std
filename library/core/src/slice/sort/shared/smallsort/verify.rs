//! Bounded SmallSort checks for selected input domains and properties.
//!
//! Module map:
//! - `network`: exchange profiles, real networks, insertion, dispatch, mutating comparators,
//!   coincident swap positions, and the large non-Copy fallback. Sortedness checks count full
//!   values only below the network width. Insertion lengths stop at 20, the callers'
//!   `MAX_LEN_ALWAYS_INSERTION_SORT` threshold, rather than a limit of the insertion helper.
//! - `merge`: stable primitives, merge, general and stable routes, and Drop counts and tags.
//!   `merge::profiles` supplies closed ordered profiles with independent full-value models.
//! - `fixed_inputs`: fixed witnesses and stable unit-ZST checks; `comparators` supplies their
//!   reading comparator. `smoke` checks the efficient-swap predicate.
//! - `types`: logical sortedness and multisets for Cell and Freeze non-Copy inputs.
//!   `forwarding_contracts`: concrete two-element forwarding contracts for Cell, u8, and
//!   Freeze non-Copy u8.
//! - `tag_permutation`: identity-tag permutation and source-type dispatch predicates. Transfer to
//!   arbitrary payloads assumes the same route moves whole elements and branches only on
//!   answers, positions, lengths, and type properties. This source-level assumption is not a
//!   generic refinement theorem; it excludes payload mutation, sortedness, and stability.
//! - `trait_model` and `trait_contracts`: conditional `ensures` on all six `small_sort`
//!   implementations, checked for nondecreasing order and preservation of every input value and
//!   its count on normal return with fixed read-only function-pointer comparators:
//!   `canonical_less_u64` on u64 at lengths 2 and 3 (stable, unstable and Freeze
//!   specializations), `canonical_less_cell` on `Cell<u8>` at length 2 (stable and unstable
//!   defaults), and `canonical_less_noncopy` on a non-Copy Freeze key at length 2 (Freeze
//!   default). The specialized unstable checks and one forwarding harness use `stub_verified`
//!   for the call to the Freeze method.
//! - `scratch_geometry`: real stable u64 sorting with separate minimal scratch and
//!   full-value counts.
//!
//! Real helper contract domains (comparators read both arguments and return arbitrary bools):
//! - `helper_contracts`: swap of u8, u64, or `[u8; 17]` in four elements; u8 in nine or thirteen;
//!   u64 insertion sort of two or three elements with any valid offset; u64 tail insertion at
//!   positions 1 through 4 in five elements; sort4 of u64 with separate source and destination
//!   arrays; u64 merge of two or four elements with separate output.
//! - `helper_contracts_wide`: swap of u8 or u64 in 32 elements with an arbitrary interior base;
//!   u64 merge of eight elements from scratch positions 32 through 39 to positions 0 through 7.
//! - `insert_tail_contracts`: u64 tail insertion at positions 1 through 15 in
//!   17 initialized elements.
//! Verified swap consumers match the nine-, thirteen-, or 32-element proofs; the sort8 consumer
//! matches the eight-element scratch merge proof. Each pair must pass with the same element
//! type, comparator, and allocation geometry. A callback-cover hook is omitted in the smaller
//! swap consumers because verified stubs bypass the comparator, while preserving its type.
//!
//! The five real helper write sets list only element or destination memory. Kani cannot express
//! the footprint of an arbitrary `FnMut`. These contracts may be used with `stub_verified` only
//! on the proved domains above and with comparators that write nowhere else; one successful
//! contract proof does not justify a new consumer. The opt-in control
//! `helper_contracts::rejects_swap_comparator_writing_outside_frame_u8` checks this restriction.
//!
//! The trait contracts allow writes to the active slice and, in the `FreezeMarker`
//! specialization of `StableSmallSortTypeImpl`, to the caller scratch. The checked comparators
//! are read-only.
//!
//! `cfg(kani_smallsort_controls)` exposes negative controls and one passing write-set check with
//! a function-item comparator. Ordinary CI leaves it unset. Run each harness individually;
//! each control must fail its named check.
//!
//! Conventions:
//! - Ordinary covers must be reachable; `run-kani.sh` does not enforce this itself.
//! - Panic stubs cut only the explicit order-violation abort path.
//! - Fixtures supply initialized input and exclusive mutable storage; region predicates
//!   check pointer geometry.
//! - Closed ordered profiles guard the exact comparator and use a pure model without
//!   invoking the callback.
//!
//! Not covered:
//! - Uninitialized-memory, value-validity, and immutable-byte permission checks, or unwinding.
//! - Trait sort guarantees for types, comparator values or kinds, lengths, or allocation
//!   layouts beyond those listed. This includes effectful `FnMut` and stability for
//!   distinguishable equal-key elements.
//! - Types, lengths, comparators, or routes beyond those listed, including aliasing, ZST,
//!   and panic cases.
//!
//! `./scripts/run-kani.sh --run list` lists ordinary roots; `--run verify-std` checks them with
//! the organizer flags, including `--no-assert-contracts`. To select a negative control, set
//! `RUSTFLAGS="--cfg kani_smallsort_controls"` and pass
//! `--kani-args --harness <full-name> --exact` to the verification command.

mod comparators;
mod fixed_inputs;
mod forwarding_contracts;
mod helper_contracts;
mod helper_contracts_wide;
mod insert_tail_contracts;
mod merge;
#[cfg(kani_smallsort_controls)]
mod mutations;
mod network;
mod scratch_geometry;
mod smoke;
mod tag_permutation;
mod trait_contracts;
pub(super) mod trait_model;
mod types;
