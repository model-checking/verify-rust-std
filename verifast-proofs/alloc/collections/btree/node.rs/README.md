# B-tree node proofs for Challenge 4

The proofs use the node's `CAPACITY` for its storage and let the tree height
and ancestor chain vary. A balancing operation owns the parent, the two
adjacent child nodes, and the headers it updates. The rest of each subtree
stays with the caller.

| Production function | Inductive proof entry |
| --- | --- |
| `NodeRef::new_internal` | `new_internal` owns the fresh root, initializes edge zero, and links the supplied subtree root at a symbolic height. The proof uses the production height conversion and calls the inclusive relink proof. |
| `Handle::insert_recursing` | `insert_recursing_for_root` invokes the production leaf dispatcher, the unbounded propagation loop and the root installation used by the three in-tree callers. The loop tracks the pending split, unvisited ancestors, completed levels, and dormant leaf slot. |
| `BalancingContext::do_merge` | The proof verifies the full production method with symbolic child heights and occupancies. It transfers the separator, repairs both edge ranges, releases the right node, and checks the normal and unwind exits. |
| `BalancingContext::merge_tracking_child_edge` | The proof checks the production index assertion, calls the proved merge with its child-returning callback, and preserves the tracked edge and its backlink on either side. |
| `BalancingContext::bulk_steal_left` | `bulk_steal_left_production` shifts the receiving key, value, and edge prefixes, transfers the donated entries to the recipient and parent, and repairs the right child's links. |
| `BalancingContext::bulk_steal_right` | `bulk_steal_right_production` transfers the right child's prefix, shifts its remaining entries left, and repairs both required edge ranges. |
| `BalancingContext::steal_left` | `steal_left_production` calls the verified bulk method with count one and verifies the offset in the returned right-child edge handle. |
| `BalancingContext::steal_right` | `steal_right_production` calls the verified bulk method with count one and constructs the handle at the original left-child edge index. |
| `NodeRef::correct_childrens_parent_links` and `correct_all_childrens_parent_links` | The half-open and inclusive range invariants track the repaired prefix and the remaining child headers. |
| `Handle::move_suffix` | `move_suffix_production` preserves the receiving node's first edge and repairs the transferred interval. |
| `NodeRef::drop_kvs` | `drop_remaining` and `resume_drop_remaining` track the initialized suffix in the main loop and the node guard. Both guard scopes are assembled from the proof and compared with production. |

## Node access and local operations

The contracts use the production node capacity and a symbolic initialized
length. They express access to the allocation with points-to predicates and
track the ownership of initialized keys and values separately from the
`MaybeUninit` storage.

| Production methods | Memory-safety argument |
| --- | --- |
| `LeafNode::new`, `InternalNode::new` | Initializes the required node fields in newly allocated typed storage. Inactive slots and a detached node's parent index remain inside `MaybeUninit`. |
| `len`, `new_edge`, `new_kv`, `first_edge`, `last_edge`, `first_kv`, `last_kv`, `left_edge`, `right_edge`, `left_kv`, `right_kv` | The length read uses a live node field. Each returned handle carries the index required by its edge or key-value role. The first and last key-value operations require a nonempty node as documented. |
| `ascend` | Needs a read fraction of the backlink fields and reads `parent_idx` only when the backlink is present. The generic proof covers the traversal-permitted marker types, including `ValMut` and `Dying`, without borrowing the key and value storage. |
| `descend` | Reads the selected initialized edge with a shared loan and verifies the height decrement. The node's key and value permissions stay with the caller. |
| `into_leaf`, `keys`, `into_kv` | Constructs shared loans from the node and the typed owners of the occupied slots. The key slice includes exactly the initialized prefix. The pair accessors borrow only the selected initialized elements after projecting their arrays. |
| `as_internal_mut`, `as_leaf_mut`, `into_leaf_mut`, `as_leaf_dying`, `key_mut`, `into_val_mut`, `into_kv_mut`, `kv_mut` | Exclusive projections transfer ownership from the source place. The end tokens identify the original places and the frame preserves untouched slots. The conversion from `MaybeUninit` requires an initialized element. |
| `into_key_val_mut_at`, `into_kv_valmut` | Raw array-to-slice coercions preserve the base pointer and attach the capacity. Indexing computes the specified slot address. Only the chosen key and value slots are borrowed, so other value loans are outside the proof's footprint. |
| `pop_internal_level`, `push_with_handle`, and both `push` implementations | Root removal reads the initialized first edge, clears the new root's backlink, and consumes the old allocation with its internal-node layout. For a leaf root, the assertion unwinds before touching the node storage. Append requires space for the new slots and initializes them while updating the length. |
| `into_key_val`, leaf `remove` | Moving an entry requires ownership of its initialized key and value. Leaf removal shifts the occupied prefixes and checks the returned edge against the shortened length. |
| `deallocate_and_ascend` | Reads the parent index only for a linked node, chooses the layout from the node's height, and consumes the matching allocation. The frame retains the ancestor storage used by the returned edge. |
| `consider_for_balancing`, `choose_parent_kv` | Copies the handle metadata and follows initialized edges next to the separator. The selection proof covers ascent from a root, either adjacent sibling, and the panic for an empty parent. The child nodes stay in the caller's frame. |
| `cast_to_leaf_unchecked`, `cast_to_internal_unchecked`, `forget_node_type`, `reborrow_mut`, and `awaken` | Validates the marker changes and the metadata carried by the resulting handle. The conversions preserve the address of the node and the slot index when present. |

## Correspondence with the library

[verify.sh](verify.sh) follows the repository's `original/` and `verified/`
layout. It diffs the snapshots of `node.rs`, `borrow.rs`, and `mem.rs`
against the checkout. It reads all three `insert_recursing` callbacks,
checks for additional call sites, and fingerprints additional library sources. The
fingerprints keep those dependencies pinned without duplicating entire
`core` and `alloc` modules.

The refinement checker compares four pairs of Rust programs. The
`// SOURCE` entries in the comparison templates copy complete functions
from the production snapshot or the annotated proof. [The refinement diff](refinement.patch)
records changes to signatures, specialized ranges, and wrapper calls.
The runner builds the views in a temporary directory.

| Comparison | Coverage |
| --- | --- |
| [Backlinks](verified/insertion.rs#L354) | Uses the shared backlink proof from `verified/insertion.rs` and copies the production `as_leaf_ptr` and `set_parent_link` for comparison. |
| [Operations](original/operations.rs.in) | Extracts the production constructors, leaf and internal insertion and split bodies, merge and steal methods, and suffix move. It also compares the arguments to the two root-install operations using the actual callback bodies and capture types from `map.rs` and `map/entry.rs`, and checks the native internal `push` and dormant-root reborrow. The [verified view](verified/operations.rs.in) draws the checked routines from [the annotated proof](verified/insertion.rs). |
| [Loops](original/loop_regions.rs.in) | Compiles the production node module with compared regions for root installation, range relinking, and tracked handles. The [verified regions](verified/loop_regions.rs.in) draw the root exit, relinking, and index calculations from the annotated proof. |
| Whole functions | Compiles the production definitions and assembles the checked insertion loop, both drop guards, and the accessor, navigation, and local-operation bodies in their production scopes. The comparison retains the owned allocator and `FnOnce` argument and follows ordinary returns and unwind cleanup edges. |

The whole-function comparison unfolds the proof helpers inside the owning
scope of `insert_recursing`. The checked entry supplies the pending split
and dormant handle. The checked loop supplies the propagation and wakeup
paths. The runner folds the checked `ascend` and its backlink and parent
construction helpers into the native `Option` operations, then diffs the
result against production. The proof reads an initialized index only when
there is a parent and establishes that its height increment is in range.
The loop's root arm calls the production `FnOnce` before awakening the
handle. All three callback projections are compiled from their production
bodies, and the projection requires the two root-install calls in their
production order. The [refinement diff](refinement.patch) folds the checked
read, internal allocation, write, and node projection into the body of
`push_internal_level`. The runner compares that body with production. It
also assembles `mem::replace` from the [verified replacement core and aborting
destructor](verified/root_replace.rs) and compares the full guard scope,
including the `take_mut` adapter, with the production MIR. The whole-function
checker follows the compiler's unwind edges without expanding calls, so it
retains the allocator and closure drop scopes as well as the cleanup for
partially moved split values.

The whole-function check also compares `do_merge`. The runner checks the
verified callback wrapper's body before emitting its `FnOnce` call in the
production scope. The checker follows a cleanup branch when the value of its
local drop flag is known.

For `choose_parent_kv`, the proof uses VeriFast's literal panic primitive.
The runner checks the pinned `unreachable_display` body and restores the
native macro with the fixed message before checking the production MIR.
The standard panic handler is a library boundary, and the branch preserves
the parent's verified resources on unwind.

For [destruction](verified/insertion.rs), the verifier checks the Dying
handle, slot projections, iterator step, and remaining suffix. The
[refinement diff](refinement.patch) folds the proved loop into the
production ranges starting at zero and at `idx + 1`. It folds the verified
key and value steps into `drop_key_val` and its value guard. The compiler
compares both guard scopes in the whole-function MIR check. This covers the
value drop after a key panic, the remaining pairs, and termination if a
destructor unwinds while the thread is already unwinding.

## Library specifications

The runner applies the B-tree library specification patch to a temporary
copy of the pinned VeriFast tool. The patch records the trusted extensions
used by the proof. [library-specs.patch](library-specs.patch)

| Primitive | Model and evidence |
| --- | --- |
| `ptr::copy` | Aligned endpoints in an owned byte span. The destination receives the source snapshot, including initialization state. Other bytes stay unchanged. Checked lemmas convert between bytes and slots, and the node contracts transfer the live `K` and `V` ownership separately. |
| `AllocatorClone::clone` | Equivalent allocation identity and a non-unwinding clone, as required by the library's unsafe trait. |
| Box and option projections | The comparison covers the production pointer conversions and the mutable `Option::Some` field projection. |
| `MaybeUninit::as_mut_ptr` | VeriFast checks the pointer cast extracted from the library body without accessing the pointee. |
| `slice::get_unchecked(usize)` and `MaybeUninit::assume_init_read` | The slice keeps the array pointer and its length. Indexing requires a live shared borrow of the in-bounds slot. The read requires an initialized value and preserves the original bits without creating another ownership of the value. The pinned core implementations provide the checked projection and read. |
| Shared prefix and `MaybeUninit::assume_init_ref` | The range preserves the base address and supplies the prefix length. Conversion to a typed reference requires the existing storage, valid alignment and extent, and initialization of the selected elements. Read permissions stay fractional. |
| `MaybeUninit::assume_init_mut` and raw slice indexing | The mutable conversion transfers the initialized slot's ownership to the resulting borrow. Raw slice indexing checks extent, alignment, and bounds. It returns the computed pointer and preserves its existing fraction of the live slot. Creating an exclusive reference requires full ownership of the slot. |
| `array::as_mut_slice` and `slice::get_unchecked_mut` | The slice keeps the array borrow's lifetime, tag, and length. An in-bounds index transfers ownership of the selected slots to the new borrow. Ending it restores the slots to the original array. The proof uses the pinned core implementations for `usize`, `Range<usize>`, and `RangeTo<usize>`. |
| `IndexMut<RangeTo<usize>>` for arrays | The pinned array and slice implementations define the coercion, delegation, and checked range calculation. The spec transfers the prefix exclusively and restores it through a slice borrow end token, including for an empty prefix. |
| `NonZero<usize>` conversions | `harness_new_internal_height_conversion` checks the checked constructor for every `usize` and the unchecked constructor at every positive value. Both preserve the input through conversion back to `usize`. |
| `From<u16> for usize` | The dependency fingerprints include the source macro implementing the widening conversion in `NodeRef::len`. |
| `MaybeUninit` storage conversion for `parent_idx` | The existing layout conversion lemmas take and return the same permission fraction. The proof reads the `u16` only when the stored option contains an initialized value. |
| `Allocator::deallocate` and allocator drop | Each deallocation consumes the right allocation with its matching layout. Typed proof entries use the fingerprinted `Allocator` safety guarantee where they need non-unwinding destruction. Generic drop retains its unwind branch, and converting an allocator ownership predicate to ordinary ownership supplies no such guarantee. |
| `ptr::drop_in_place` | The pinned VeriFast contract consumes the initialized value and its ownership. The slot stays available as storage on either exit. The patched frontend follows the compiler's unwind action for a MIR `Drop`. |
| `ptr::read` of a Dying handle | `duplicate_dying` proves the read from initialized handle storage. It copies the handle metadata and frames the node's slot ownership through the read. |
| Tuple ownership | The callback proofs use componentwise ownership for one- and two-element tuples, following the pinned prelude's tuple rules. |
| `RangeInclusive<usize>` | For a fresh iterator with `end < usize::MAX`, `harness_relink_inclusive_range_next` checks the initialization and step of the production iterator. |

## Maintaining the comparison

When production changes, review the checkout against the `original/`
snapshots and update the affected comparison templates and diffs together.
Rerun the pinned checker and the mutation tests after retargeting a
comparison. The [refinement.patch](refinement.patch) adapts the compiler inputs for the
runtime-inert safety attributes and the pinned compiler's abort spelling.

## Running the checks

The repository's VeriFast runner calls `verify.sh --ci` on Linux x86_64.
This mode builds the pinned tool in a temporary directory and runs the
proofs, MIR comparisons, and negative suite. Positive VeriFast runs reject
a prover diagnostic about inconsistent axiom instantiations. The runner uses
Bash, Git, and the pinned Rust and VeriFast tools. [The negative diff](negative/mutations.patch)
groups 32 independent cases applied to temporary copies.
[Repository runner](../../../../check-verifast-proofs.sh) · [VeriFast patches and regressions](verifast-patches/README.md)

The negative suite changes the fit-at-capacity decision, root edge write
and replacement guard, split suffix and relink, merge layout and tracked
edge, steal ranges and separator, and the first destination edge in a
suffix transfer. It also checks rejection of an incorrect drop slot, a
suppressed value guard, and an incorrect cleanup start. The script tests
both the verifier and the MIR comparison where the mutation changes a
verified memory operation. Changing the merge deallocation layout also
fails the whole-function unwind comparison.
It also rejects a non-allocator's false no-unwind contract, a changed
production callback even without the source fingerprint check, an early
release of the root replacement guard, and a change in destructor order
visible only on unwind. The production dispatch and ascend mutations check
that a changed fullness test or parent index fails the source correspondence.
The whole-function comparison also rejects an early return that skips a
parent split. The drop proof's source fold rejects using the same slot again
on each iteration.
The UB cases read one slot past the initialized prefix within the array's
capacity, write through a shared view, borrow an already borrowed key
exclusively, and construct a `NonNull` from a null pointer. Each exercises
the corresponding initialization, permission, or validity obligation.

Kani uses the pinned tool and default checks for the loop-free constructors,
accessors, and local operations. The harnesses cover every function in the
challenge's 26-function list with symbolic node occupancy and concrete
allocations. Their contracts have matching `proof_for_contract` harnesses.
Covers exercise branches such as empty and full nodes, either balancing
side, and successful allocation release. The B-tree harness group uses
zero explicit `assume`, stubs, and `#[kani::unwind]` annotations.

```sh
./scripts/run-kani.sh --path . --kani-args --harness-timeout 1800 --jobs 1 \
    --harness collections::btree::node::verify::
```
