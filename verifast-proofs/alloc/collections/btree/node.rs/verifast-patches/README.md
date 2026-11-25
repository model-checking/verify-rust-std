# VeriFast changes for the B-tree proofs

The B-tree verification entry builds VeriFast **26.10** at
`f76012fb518703b1d98e243ac4f487f16877cfcb` with the 14 patches in this
directory. On 2026-11-24, the latest tagged release was 26.10. Upstream
`master` at `0a83dba42db7ce0b445034ece5298afe980e57dc` adds one build
commit. The changes to the Rust frontend and checker select the toolchain
through `RUSTUP_TOOLCHAIN`. The affected MIR lowering, refinement rules,
and Rust specifications match the release. [Release][release] · [Source comparison][compare]

## Necessity and upstream status

Each row identifies the production obligation served by the patch and the
available rollback or regression evidence. The contracts rely on the
pointer, ownership, and lifetime premises described in the row.

| Patch | Scope and rollback result | Upstream status |
| --- | --- | --- |
| 0001 | Refinement compares the exported raw pointer kind and place, including projections, and takes account of address-taken locals. The existing normalization is limited to metadata and the simple mutable-reference reservation lowering. Removing the paired rule blocks production MIR comparison. Narrowing the normalization to metadata alone breaks the upstream reservation regression. | [#1062][raw-pr] addresses [#1040][raw-issue]. It compares place and mutability. Its checker change passed all three B-tree MIR comparisons when substituted into the otherwise patched tool. The more conservative kind export is local. [#1064][hardening] includes the same checker change as #1062. Both PRs are open. |
| 0002 | Box dereference lowering extracts the normal result of the pointer projection. The raw projection cannot unwind and preserves the owned Box storage. Reverting the lowering leaves a `fn_outcome` where the generated code needs a pointer. | [#786][box-base] provides the merged baseline Box support. I found no PR for this outcome fix. |
| 0003 | Fixed-array MIR projections retain the evaluated index and the element type. Reads and stores compare the corresponding operand and place, and the Rust MIR bounds assertion stays in the proof. Disabling the projection blocks translation of the production edge write. | [#1048][const-generic] partially overlaps typesystem constant operands. [#994][arrays] improves static-array handling. Both are open and leave this MIR projection unsupported. |
| 0004 | Opening a points-to assertion for an initialized array reuses its stored element list. The uninitialized case still uses its separate predicate. Without the fix the proof loses the known values when it reopens the array. | The initialized `Term` case in open [#994][arrays] already implements the same fix. |
| 0005 | Shared array unsizing preserves the reference's address, tag, and lifetime, and adds the static length. The `usize` unchecked read requires an in-bounds element and its shared loan. Removing the coercion blocks the production edge read used by relinking. | Merged [#1001][shared-slice] supplies shared slice types. I found no equivalent array-to-slice projection PR. |
| 0006 | Mutable array unsizing preserves the same loan. An in-bounds `usize`, `Range`, or `RangeTo` projection transfers exclusive ownership and restores it when the loan ends. The negative regression attempts a write through the original pointer while the element is borrowed. Removing mutable coercion blocks the production transfers. | Merged [#1015][mut-slice] and [#1027][slice-contracts] supply slice types and generated in-out contracts. I found no PR for these projection rules. |
| 0007 | The explicit `track_ref_creation` directive uses the existing fresh-mutable-reference rule on the selected places. The rule consumes the original points-to ownership and records the origin and end token. Without it the proof lacks the loan token for a production node projection. | I found no equivalent opt-in directive. |
| 0008 | Array `IndexMut<RangeTo<usize>>` requires that the end is within the static length and consumes exactly the prefix's permission. The regression supplies twelve slots to an eleven-element array type so an oversized end is rejected by the bound itself. Without the specialization, the native split's prefix projection has no dispatch rule. | Related to [#994][arrays] and the merged slice support. I found no equivalent `IndexMut` rule. |
| 0009 | The exporter folds an adjacent, retag-free Box copy and pointer projection through a mutable Box reference when that projection is the temporary's sole read. The checker keeps the source dereference and Box pointer projection. Without the fold the full split proof cannot recover the borrowed Box's points-to permission. | [#786][box-base] is the baseline. I found no PR for this MIR shape. |
| 0010 | Address-taken analysis continues after `merge_fractions`. This restores traversal of the remaining statements, with no change to the proof rules for fractions. The split proof and a standalone raw-borrow regression fail without it. | Merged [#1023][address-local] addresses locals in projection clauses. I found no fix for the `merge_fractions` traversal. |
| 0011 | Rust field provenance cannot determine the parent address. The patch removes the incompatible inverse axiom. When restored, the B-tree run reports inconsistent axiom instantiation and still exits successfully with fewer verified statements. The regression rejects equality of projections from different addresses. | Merged [#538][c-provenance] fixed a related axiom in the C prelude. The Rust axiom remains on master. |
| 0012 | MIR `Drop` follows the compiler's normal and unwind actions. Strict refinement compares cleanup edges from calls, drops, and assertions, including projected drop places. It follows a copied plain local's branch when its value is already a known boolean. The merge comparison needs this rule for a compiler drop flag after the key has moved. Symbolic and address-taken locals still use the regular comparison. The generic-drop, layout, and changed-cleanup-order regressions check these rules. | Merged [#664][unwind] provides the general unwind handling. Open [#1046][manual-drop] concerns `ManuallyDrop::new`. Open [#1036][nested] and [#1058][nested2] concern nested specifications. I found no matching fix for `Drop` terminators or strict drop-flag comparison. |
| 0013 | `NodeRef::keys` needs shared `RangeTo<usize>` indexing and a typed slice view of the initialized prefix. Indexing preserves the base address and shortens the metadata. Scalar `assume_init_mut` transfers an initialized slot and supplies its borrow end token. The B-tree regressions reject an uninitialized prefix and a second exclusive borrow. | Neither the current release nor master supplies these dispatch and initialized-view rules. [#1001][shared-slice] and [#1015][mut-slice] supply the underlying slice reference types. |
| 0014 | `ValMut` uses raw array unsizing and raw slot indexing to leave the other value loans in place. The index checks pointer geometry and preserves the existing permission for the addressed slot. The shared projection requires an initialized slot, and the exclusive projection requires full ownership. | Open [#1061][raw-slice-fields] adds type interpretations for raw slice pointer fields. Open [#1035][raw-slice-aggregate] lowers construction from data and metadata. The coercion, indexing, and initialized-slot operations in this patch are separate. |

The B-tree proof also installs a temporary set of library contracts described
in the [proof README](../README.md#library-specifications). These are reviewed
as specifications in addition to the frontend patches. Open [#1037][tuple1]
and [#1057][tuple2] overlap its one- and two-element tuple ownership rules.

## Upstream submissions

Follow [#1062][raw-pr] and [#994][arrays] for the overlapping changes and
discuss exporting the raw pointer kind in #1062. The remaining changes fit
seven new PRs.

| Proposed PR | Local patches | Review scope |
| --- | --- | --- |
| Rust Box pointer projection | 0002, 0009 | Extract the normal result of Box pointer projection and handle the borrowed-Box MIR shape. |
| Fixed-array MIR projections | 0003 | Carry the evaluated index and element type through MIR export and refinement. Coordinate constant operands with [#1048][const-generic]. |
| Array-to-slice projections | 0005, 0006, 0008, 0013, 0014 | Cover shared unsizing, exclusive element and range borrows, checked prefix indexing, and raw offset calculation. Include the initialized-view contracts and rejection tests. |
| Scoped mutable reference creation | 0007 | Track the transfer and return of a mutable place's permissions. |
| Address scanning after `merge_fractions` | 0010 | Continue scanning the remaining statements and verify the standalone raw-borrow regression. |
| Rust field provenance | 0011 | Remove the inconsistent Rust axiom and keep the distinct-address regression with the fix. |
| Rust MIR `Drop` unwind | 0012 | Follow compiler cleanup actions in the verifier and in direct refinement comparisons. Include known drop-flag handling, the generic destructor regression, and the cleanup-order regression. |

Submit the provenance and `Drop` fixes first so each can be reviewed and
merged independently. The scoped borrow change builds on the mutable borrow
dispatch in 0006. Run the borrowed-Box regression on top of that change
because the regression uses its tracking directive. Refresh overlapping
translator and test registration hunks against each PR's base.

## Reproducing the B-tree check

Run the same command as the repository's VeriFast runner from a Linux
x86_64 checkout. The build compiles the verifier, refinement checker,
and exporter together with a common MIR schema.

```sh
bash verifast-proofs/alloc/collections/btree/node.rs/verify.sh --ci
```

On patched 26.10, all 48 upstream Rust refinement-checker cases and 11
patch-registered Rust verifier cases produced their expected outcomes.
Stock 26.10 loses the initialized array values in `keep_array`, reports
an axiom inconsistency in `field_projection_addresses.rs`, and accepts the
false no-unwind contract in `drop_cleanup.rs`. The corresponding patched
tests pass with their expected rejections. All 14 patches and the
B-tree library specification diff apply to the inspected `master` revision.

The patches include regression entries in the upstream Rust and refinement
testsuites. The B-tree negative suite independently checks the production
proof and its correspondence.

[release]: https://github.com/verifast/verifast/releases/tag/26.10
[compare]: https://github.com/verifast/verifast/compare/26.10...0a83dba42db7ce0b445034ece5298afe980e57dc
[raw-issue]: https://github.com/verifast/verifast/issues/1040
[raw-pr]: https://github.com/verifast/verifast/pull/1062
[hardening]: https://github.com/verifast/verifast/pull/1064
[box-base]: https://github.com/verifast/verifast/pull/786
[const-generic]: https://github.com/verifast/verifast/pull/1048
[arrays]: https://github.com/verifast/verifast/pull/994
[shared-slice]: https://github.com/verifast/verifast/pull/1001
[mut-slice]: https://github.com/verifast/verifast/pull/1015
[slice-contracts]: https://github.com/verifast/verifast/pull/1027
[address-local]: https://github.com/verifast/verifast/pull/1023
[c-provenance]: https://github.com/verifast/verifast/pull/538
[unwind]: https://github.com/verifast/verifast/pull/664
[manual-drop]: https://github.com/verifast/verifast/pull/1046
[nested]: https://github.com/verifast/verifast/pull/1036
[nested2]: https://github.com/verifast/verifast/pull/1058
[tuple1]: https://github.com/verifast/verifast/pull/1037
[tuple2]: https://github.com/verifast/verifast/pull/1057
[raw-slice-fields]: https://github.com/verifast/verifast/pull/1061
[raw-slice-aggregate]: https://github.com/verifast/verifast/pull/1035
