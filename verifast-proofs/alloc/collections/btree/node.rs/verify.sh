#!/bin/bash

set -euo pipefail

cd "$(dirname "$0")"
proof_dir=$PWD
library=$(cd ../../../../../library && pwd)
work_dir=$(mktemp -d)
work_dir=$(cd "$work_dir" && pwd)
trap 'rm -rf -- "$work_dir"' EXIT

if [[ ${1:-} == --ci ]]; then
    tool="$work_dir/tool"
    mkdir "$tool"
    bash verifast-patches/build.sh "$tool"
    VERIFAST_HOME="$tool" bash verify.sh
    VERIFAST_HOME="$tool" bash verify.sh --negative
    exit 0
fi

: "${VERIFAST_HOME:?Build the B-tree VeriFast tool with verifast-patches/build.sh}"
verifast_home=$(cd "$VERIFAST_HOME" && pwd)
export LD_LIBRARY_PATH="$verifast_home/bin${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

cp -a original verified "$work_dir/"
cd "$work_dir"
# Keep git apply independent of the user's checkout when TMPDIR is inside it.
export GIT_CEILING_DIRECTORIES=$(dirname "$work_dir")

check_sources() {
    local btree="$library/alloc/src/collections/btree"
    local source uses
    for source in node.rs mem.rs borrow.rs; do
        if ! diff -u "$btree/$source" "original/$source"; then
            echo "B-tree production snapshot changed: $source" >&2
            return 1
        fi
    done
    (cd "$library" && sha256sum --quiet --strict -c "$work_dir/original/dependencies.sha256") || return
    # The empty-parent branch uses the verifier's literal-panic primitive.
    # Its production expansion formats this same static string and panics.
    local panic_body
    panic_body=$(proof_body 'pub fn unreachable_display<' "$library/core/src/panicking.rs") || return
    if [[ $panic_body != '    panic_fmt(format_args!("internal error: entered unreachable code: {}", *x));' ]]; then
        echo 'B-tree empty-parent panic expansion changed' >&2
        return 1
    fi
    uses=$(
        cd "$btree"
        LC_ALL=C grep -Rnw --include='*.rs' --exclude=tests.rs --exclude-dir=tests insert_recursing .
    ) || return
    # assemble_views reads the two cursor callbacks and the vacant-entry
    # callback. The remaining occurrence is the production definition.
    if [[ $(wc -l <<< "$uses") != 4 ]]; then
        echo 'B-tree insert_recursing call sites changed' >&2
        return 1
    fi
}

# Fill the named function positions with their complete source text. The
# declarations being compared may use different enclosing impls, lifetimes,
# or wrapper calls. The checked-in diffs record those adaptations.
# SOURCE_IN_IMPL disambiguates overloads using the surrounding impl line.
copy_regions() {
    local template=$1
    shift
    awk '
        FNR == NR {
            lines[++size] = $0
            if (/^impl[< ]/) scope = $0
            if ($0 == "}") scope = ""
            if (sub(/^\/\/ SOURCE /, "")) {
                selections[size] = $0
            } else if (sub(/^\/\/ SOURCE_IN_IMPL /, "")) {
                selections[size] = scope SUBSEP $0
            }
            if (size in selections) requested[selections[size]] = $0
            next
        }
        !copying {
            if (FNR == 1 || $0 == "}") scope = ""
            if (/^impl[< ]/) scope = $0
            signature = ($0 in requested) ? $0 : scope SUBSEP $0
            if (signature in requested) {
                match($0, /^ */)
                closing = substr($0, 1, RLENGTH) "}"
                region[signature] = ""
                copying = 1
            }
        }
        copying {
            region[signature] = region[signature] $0 "\n"
            if ($0 == closing) {
                seen[signature]++
                copying = 0
            }
        }
        END {
            for (name in requested) {
                if (seen[name] != 1) {
                    print "Expected exactly one source region: " requested[name] > "/dev/stderr"
                    exit 1
                }
            }
            for (i = 1; i <= size; i++) {
                if (i in selections) printf "%s", region[selections[i]]
                else print lines[i]
            }
        }
    ' "$template" "$@"
}

# Use each production callback as the original side of the root comparison.
# Project just the arguments to the final install, whose two operations
# (push_internal_level and push) are compared separately.
project_root_callbacks() {
    awk '
        FILENAME != ARGV[3] {
            if (!active) {
                if (FILENAME == ARGV[1] &&
                    /^        let handle = edge[.]insert_recursing[(]key, value, self[.]alloc[.]clone[(][)], [|]ins[|] [{]$/) {
                    ++cursors
                    active = ++count
                    end = "        });"
                } else if (FILENAME == ARGV[2] &&
                    /^            Some[(]handle[)] => handle[.]insert_recursing[(]self[.]key, value, self[.]alloc[.]clone[(][)], [|]ins[|] [{]$/) {
                    ++entries
                    active = ++count
                    end = "            }),"
                }
            } else if ($0 == end) {
                if (!installed) failed = 1
                active = installed = 0
            } else if ($0 ~ /^ +root[.]push_internal_level[(]self[.]alloc[.]clone[(][)][)][.]push[(]ins[.]kv[.]0, ins[.]kv[.]1, ins[.]right[)]$/) {
                if (installed) failed = 1
                installed = 1
                callback[active] = callback[active] \
                    "            (root, self.alloc.clone(), ins.kv.0, ins.kv.1, ins.right)\n"
            } else {
                if (installed && $0 !~ /^ *(\/\/.*)?$/) failed = 1
                callback[active] = callback[active] $0 "\n"
            }
            next
        }
        /^\/\/ ROOT_CALLBACK [1-3]$/ {
            ++used[$3]
            printf "%s", callback[$3]
            next
        }
        /^pub struct (BTreeMap|CursorMutKey|VacantEntry)</ { capture_type = 1 }
        capture_type {
            # These declarations moved from alloc to the standalone crate root.
            sub(/^    #\[unstable[(][^]]*[)]\] /, "    ")
            sub(/^    pub[(]super[)] /, "    ")
            gsub(/crate::boxed::Box</, "Box<")
            gsub(/node::Root</, "Root<")
            if ($0 == "}") capture_type = 0
        }
        { print }
        END {
            if (failed || active || cursors != 2 || entries != 1 ||
                used[1] != 1 || used[2] != 1 || used[3] != 1) {
                print "B-tree root callback shape changed" > "/dev/stderr"
                exit 1
            }
        }
    ' "$1" "$2" "$3"
}

# Read the executable body of a named function in the annotated proof.
proof_body() {
    awk -v signature="$1" '''
        index($0, signature) == 1 {
            ++found
            match($0, /^ */)
            indent = substr($0, 1, RLENGTH)
            header = 1
        }
        header && ($0 == indent "{" || /^ *[)] ->.* [{]$/ ||
                   (index($0, signature) == 1 && /[{]$/)) {
            header = 0
            body = 1
            next
        }
        body && $0 == indent "}" { body = 0; ++closed; next }
        !body { next }
        /^[[:space:]]*\/\*@[[:space:]]*$/ { ghost = 1 }
        ghost && /^[[:space:]]*@\*\/[[:space:]]*$/ { ghost = 0; next }
        ghost || /^[[:space:]]*(\/\/.*)?$/ { next }
        {
            gsub(/\/\*@::<[^@]*>@\*\//, "")
            gsub(/\/\*@~mut@\*\/ /, "")
            if (index($0, "/*@")) exit 1
            print substr($0, length(indent) + 1)
        }
        END { if (found != 1 || closed != 1 || ghost) exit 1 }
    ' "$2"
}


# Inline the proved entry and handoff in the owning production scope.
# Keep the FnOnce invocation in the root arm. Its three implementations
# are checked through the root projections and the root-install refinement.
compose_insert_recursing() {
    local entry clone handoff loop
    entry=$(proof_body '    unsafe fn insert_recursing_for_root<' verified/insertion.rs) || return
    clone=$(proof_body '    unsafe fn clone_and_insert<' verified/insertion.rs) || return
    handoff=$(proof_body 'unsafe fn resume_after_leaf_insert_for_root<' verified/insertion.rs) || return
    loop=$(proof_body 'unsafe fn propagate_split_for_root<' verified/insertion.rs) || return

    if [[ "$entry" != '    let initial = unsafe { self.clone_and_insert(key,val,alloc) };
    let result = unsafe { resume_after_leaf_insert_for_root(initial,alloc,root_slot,root_allocator) };
    result' || "$clone" != '    unsafe { self.insert(key, val, alloc.clone()) }' ]]; then
        echo 'B-tree proved insertion entry changed' >&2
        return 1
    fi

    printf '%s\n' '    let initial = self.insert(key, value, alloc.clone());'
    awk '
        NR == 1 && $0 == "    let (pending, inserted) = match initial {" {
            print "    let (mut split, inserted) = match initial {"
            ++binding
            next
        }
        $0 == "    let result = unsafe { propagate_split_for_root(pending, inserted, alloc, root_slot, root_allocator) };" {
            ++handoff
            if ((getline) != 1 || $0 != "    result") exit 1
            if ((getline) != 0) exit 1
            next
        }
        { print }
        END { if (binding != 1 || handoff != 1) exit 1 }
    ' <<< "$handoff" || return

    awk '
        NR == 1 && $0 == "    let mut split = initial_split;" { ++binding; next }
        $0 == "                return unsafe { finish_root_split(payload, inserted, root_slot, root_allocator) };" {
            ++root
            print "                split_root(payload);"
            print "                return unsafe { inserted.awaken() };"
            next
        }
        { print }
        END { if (binding != 1 || root != 1) exit 1 }
    ' <<< "$loop"
}

# Fold the checked drop steps into the two native guard scopes. The diff
# connects the first and cleanup ranges to drop_remaining, and the value
# destructor to both exits from drop_pair.
collect_drop_bodies() {
    local signature
    while IFS= read -r signature; do
        if [[ $signature == '// body '* ]]; then
            printf '%s\n' "$signature"
        else
            printf '// %s\n' "$signature"
            proof_body "$signature" verified/insertion.rs || return
        fi
    done <<'EOF'
// body drop_kvs
unsafe fn drop_remaining<
unsafe fn drop_at<
unsafe fn duplicate_dying<
    unsafe fn new_dying_kv(
unsafe fn resume_drop_remaining<
// body drop_key_val
unsafe fn finish_drop_value<
    unsafe fn drop_key_val_step(
    unsafe fn project_drop_slots<
unsafe fn drop_pair<
unsafe fn drop_initialized_slot<
unsafe fn drop_guarded_value<
    unsafe fn drop_value_guard(
unsafe fn drop_slot_production<
EOF
}

assemble_verified_operations() {
    copy_regions verified/operations.rs.in verified/insertion.rs |
        sed 's/^unsafe fn repair_one__VeriFast_wrapper</unsafe fn repair_one</' > verified/operations.rs || return
    git apply --whitespace=nowarn --include=verified/operations.rs "$proof_dir/refinement.patch"
}

assemble_views() {
    local btree="$library/alloc/src/collections/btree"
    # Reuse the backlink proof from the insertion program.
    sed -e '/^#!\[feature(slice_ptr_get)\]$/d' -e '/^    impl BorrowType for Dying {}$/d' \
        -e '/^\/\/ END_BACKLINK_METHODS$/q' \
        verified/insertion.rs > verified/backlinks.rs
    printf '\nfn main() {}\n' >> verified/backlinks.rs
    cp verified/backlinks.rs original/backlinks.rs.in
    copy_regions original/operations.rs.in original/node.rs original/borrow.rs \
        "$btree/map.rs" "$btree/map/entry.rs" > original/operations.rs
    copy_regions original/loop_regions.rs.in original/node.rs > original/loop_regions.rs
    copy_regions verified/loop_regions.rs.in verified/insertion.rs > verified/loop_regions.rs
    collect_drop_bodies > verified/drop-bodies.rs || return
    {
        echo '// BEGIN_ROOT_INSTALL'
        proof_body 'unsafe fn install_root_split<' verified/insertion.rs || return
        echo '// END_ROOT_INSTALL'
    } > verified/root-level-body.rs
    {
        echo '// BEGIN_ASCEND'
        proof_body '    unsafe fn ascend(' verified/insertion.rs || return
        echo '// END_ASCEND'
        echo '// BEGIN_FROM_INTERNAL'
        proof_body '    unsafe fn from_internal(' verified/insertion.rs || return
        echo '// END_FROM_INTERNAL'
        echo '// BEGIN_OPEN_NEXT_PARENT'
        proof_body 'unsafe fn open_next_parent<' verified/insertion.rs || return
        echo '// END_OPEN_NEXT_PARENT'
    } > verified/ascend-body.rs

    mkdir portable
    cp original/{node,borrow,mem}.rs portable/
    cp original/loop_crate.rs portable/main.rs
    git apply --whitespace=nowarn --exclude=verified/operations.rs "$proof_dir/refinement.patch" || return
    assemble_verified_operations || return
    mv original/operations.rs original/operations-template.rs
    project_root_callbacks \
        "$btree/map.rs" "$btree/map/entry.rs" \
        original/operations-template.rs > original/operations.rs
    copy_regions original/backlinks.rs.in original/node.rs > original/backlinks.rs
    # Standalone compilation only needs the production runtime prefix.
    sed -i '/^#\[cfg(test)\]$/,$d' portable/{node,borrow}.rs
}

check_ascend_body() {
    # The comparison diff folds the checked backlink step into the native
    # Option combinators and restores the generic traversal assertion.
    {
        echo '// BEGIN_ASCEND'
        proof_body '    pub(super) fn ascend(' portable/node.rs || return
        echo '// END_ASCEND'
        echo '// BEGIN_FROM_INTERNAL'
        proof_body '    fn from_internal(' portable/node.rs || return
        echo '// END_FROM_INTERNAL'
    } > original/ascend-body.rs
    if ! diff -u original/ascend-body.rs verified/ascend-body.rs; then
        echo 'B-tree production ascend differs from the checked parent step' >&2
        return 1
    fi
    check_link_ascend
}

check_link_ascend() {
    local common link expected actual
    while IFS='|' read -r common link; do
        expected=$(proof_body "$common" verified/insertion.rs) || return
        actual=$(proof_body "$link" verified/insertion.rs |
            sed -e 's/read_parent_link(/open_next_parent(/' \
                -e '/^    const { assert!(BorrowType::TRAVERSAL_PERMIT); }$/d') || return
        diff -u <(printf '%s\n' "$expected") <(printf '%s\n' "$actual") || return
    done <<'EOF'
unsafe fn open_next_parent<|unsafe fn read_parent_link<
    unsafe fn ascend(|    unsafe fn ascend_from_link(
EOF
    expected=$(proof_body '    pub const fn ok(self)' "$library/core/src/result.rs") || return
    actual=$(proof_body 'unsafe fn dying_result_ok<' verified/insertion.rs |
        sed 's/^    match value {/    match self {/') || return
    diff -u <(printf '%s\n' "$expected") <(printf '%s\n' "$actual")
}

assemble_loops() {
    local side
    for side in original verified; do
        mkdir -p "$side/loops"
        cp portable/*.rs "$side/loops/"
        cat "$side/loop_regions.rs" >> "$side/loops/node.rs"
    done
}

# Put the verified replacement core and aborting destructor in the native
# guard scope. The strict MIR check also compares take_mut's closure adapter.
assemble_root_replacement() {
    cat <<'EOF'
use core::{mem, ptr};

#[allow(dead_code)]
#[inline]
pub(super) fn take_mut<T>(v: &mut T, change: impl FnOnce(T) -> T) {
    replace(v, |value| (change(value), ()))
}

#[inline]
pub(super) fn replace<T, R>(v: &mut T, change: impl FnOnce(T) -> (T, R)) -> R {
    struct PanicGuard;
    impl Drop for PanicGuard {
        fn drop(&mut self) {
EOF
    proof_body '    fn drop(&mut self)' verified/root_replace.rs | sed 's/^/        /' || return
    cat <<'EOF'
        }
    }
    let guard = PanicGuard;
EOF
    proof_body 'unsafe fn replace_core<' verified/root_replace.rs | awk '
        /^    ret$/ { print "    mem::forget(guard);"; ++returned }
        { print }
        END { if (returned != 1 || $0 != "    ret") exit 1 }
    ' || return
    echo '}'
}

collect_access_bodies() {
    local method signature callback
    # The prover checks the generic wrapper. In the owning scope, emit its
    # native call so the checker can compare cleanup without inlining.
    callback=$(proof_body 'unsafe fn call_merge__VeriFast_wrapper<' verified/insertion.rs) || return
    if [[ $callback != '    finish(parent, child)' ]]; then
        echo 'B-tree merge callback body changed' >&2
        return 1
    fi
    while read -r method signature; do
        printf '// body %s\n' "$method"
        proof_body "    unsafe fn $signature" verified/insertion.rs |
            sed -e 's/\.\(merge_len\|relink_len\)(/.len(/g' \
                -e 's/Handle::new_relink_edge(/Handle::new_edge(/g' \
                -e 's/Handle::new_navigation_kv(/Handle::new_kv(/g' \
                -e 's/\.\(key\|val\|edge\)_area_\(slot\|prefix\|range\)_mut(/.\1_area_mut(/g' \
                -e 's/\.relink_range(/.correct_childrens_parent_links(/g' \
                -e 's/unsafe { call_merge__VeriFast_wrapper(finish, parent_node, left_node) }/result(parent_node, left_node)/' \
                -e 's/\.cast_node_to_leaf(/.cast_to_leaf_unchecked(/g' \
                -e 's/^\( *\)panic!("internal error: entered unreachable code: empty internal node")$/\1unreachable!("empty internal node")/' \
                -e 's/unsafe { dying_result_ok(self\.ascend_from_link()) }/self.ascend().ok()/' || return
    done <<'EOF'
len merge_len(
new_edge new_relink_edge(
new_kv new_navigation_kv(
first_edge first_edge(
last_edge last_edge(
first_kv first_kv(
last_kv last_kv(
left_edge left_edge(
right_edge right_edge(
left_kv left_kv(
right_kv right_kv(
descend descend(
as_internal_ptr as_internal_ptr(
into_leaf into_leaf(
keys keys<
into_kv into_kv(
as_leaf_mut as_leaf_mut<
into_leaf_mut into_leaf_mut(
as_leaf_dying as_leaf_dying<
as_internal_mut as_internal_mut<
key_mut key_mut<
kv_mut kv_mut<
into_val_mut into_val_mut(
into_kv_mut into_kv_mut(
into_key_val_mut_at into_key_val_mut_at(
into_kv_valmut into_kv_valmut(
into_key_val into_key_val(
push_with_handle push_with_handle<
push_leaf push_leaf<
borrow_mut borrow_mut<
cast_to_internal_unchecked cast_to_internal_unchecked(
clear_parent_link clear_parent_link<
pop_internal_level pop_internal_level<
deallocate_and_ascend deallocate_and_ascend<
remove remove<
consider_for_balancing consider_for_balancing(
do_merge do_merge_production<
choose_parent_kv choose_parent_kv(
cast_node_to_leaf cast_node_to_leaf(
cast_handle_to_leaf cast_handle_to_leaf(
reborrow_node_mut reborrow_mut<
reborrow_handle_mut reborrow_handle_mut<
awaken_node awaken<'a>(self) -> NodeRef
awaken_handle awaken<'a>(self) -> Handle
forget_leaf_edge forget_leaf_edge(
forget_internal_edge forget_internal_edge(
forget_leaf_kv forget_leaf_kv(
EOF
}

assemble_whole_functions() {
    local side
    # Compare the folded root installation with the production method.
    # Identical closure text also preserves its Rust capture and call scope.
    {
        echo '// BEGIN_ROOT_INSTALL'
        proof_body '    pub(super) fn push_internal_level<' portable/node.rs || return
        echo '// END_ROOT_INSTALL'
    } > original/root-level-body.rs
    diff -u original/root-level-body.rs verified/root-level-body.rs || return

    for side in original verified; do
        mkdir -p "$side/whole"
        cp portable/*.rs "$side/whole/"
    done
    {
        echo '// body insert_recursing'
        compose_insert_recursing || return
        collect_access_bodies || return
        cat verified/drop-bodies.rs
    } > whole-bodies.rs
    awk '
        FNR == NR {
            if (/^\/\/ body /) {
                name = $3
                if (name in body) exit 1
                body[name] = ""
                next
            }
            body[name] = body[name] "    " $0 "\n"
            next
        }
        /^impl[< ]/ {
            impl_header = $0
            handle_impl = / Handle</
        }
        !skipping && /^    (pub[(]super[)] )?(unsafe )?fn [[:alnum:]_]+[<(]/ {
            name = $0
            sub(/^.* fn /, "", name)
            sub(/[<(].*$/, "", name)
            if (name == "push" && / -> \*mut V/) name = "push_leaf"
            if (name == "reborrow_mut") name = handle_impl ? "reborrow_handle_mut" : "reborrow_node_mut"
            if (name == "cast_to_leaf_unchecked") name = handle_impl ? "cast_handle_to_leaf" : "cast_node_to_leaf"
            if (name == "awaken") name = handle_impl ? "awaken_handle" : "awaken_node"
            if (name == "forget_node_type" && handle_impl) {
                if (impl_header ~ /marker::Internal>, marker::Edge>/) name = "forget_internal_edge"
                if (impl_header ~ /marker::Leaf>, marker::Edge>/) name = "forget_leaf_edge"
                if (impl_header ~ /marker::Leaf>, marker::KV>/) name = "forget_leaf_kv"
            }
            if (name in body) {
                header = 1
                ++found[name]
            }
        }
        header && /[{]$/ {
            print
            printf "%s", body[name]
            header = 0
            skipping = 1
            next
        }
        skipping && /^    }$/ { skipping = 0; ++closed[name] }
        !skipping { print }
        END {
            for (name in body) if (found[name] != 1 || closed[name] != 1) exit 1
        }
    ' whole-bodies.rs portable/node.rs > verified/whole/node.rs || return
    assemble_root_replacement > verified/whole/mem.rs
}

verify_proof() {
    "$@" 2>&1 | tee verification.log
    if grep -Fq 'Detected an inconsistency after axiom instantiations' verification.log; then
        echo "VeriFast reported an inconsistent proof state." >&2
        return 1
    fi
}

refine() {
    "$verifast_home/bin/refinement-checker" --rustc-args '--edition=2024' "$@"
}

refine_whole_functions() {
    refine --check-unwind original/whole/main.rs verified/whole/main.rs
}

proof() {
    "$work_dir/verifast/bin/verifast" -skip_specless_fns -allow_dead_code "$@"
}

rejected() {
    local diagnostic=$1
    shift
    if "$@" > rejection.log 2>&1 || ! grep -Fq -- "$diagnostic" rejection.log; then
        cat rejection.log
        return 1
    fi
    printf '%s\n' "$diagnostic"
}

mutate() {
    local patch
    patch=$(awk -v label="# Case $1" '
        $0 == label { seen++; selected = 1; next }
        /^# Case / { selected = 0; next }
        selected { print }
        END { if (seen != 1) exit 1 }
    ' "$proof_dir/negative/mutations.patch")
    shift

    git apply --whitespace=error <<< "$patch"
    "$@"
    git apply --whitespace=error -R <<< "$patch"
}

reject_proof() {
    local diagnostic=$1 file=$2 signature=$3 line
    line=$(awk -v signature="$signature" 'index($0, signature) == 1 { print NR; exit }' "$file")
    test -n "$line"
    rejected "$diagnostic" proof -focus "$file:$line" "$file"
}

reject_loop() {
    copy_regions verified/loop_regions.rs.in verified/insertion.rs > verified/loop_regions.rs || return
    git apply --whitespace=nowarn --include=verified/loop_regions.rs "$proof_dir/refinement.patch" || return
    assemble_loops
    rejected "$1" refine original/loops/main.rs verified/loops/main.rs
}

reject_insert_loop() {
    assemble_whole_functions || return
    rejected 'The constants FnDef node::SplitResult::' refine_whole_functions
}

reject_keys_prefix() {
    reject_proof 'Cannot prove std::mem::initialized_slots' verified/insertion.rs '    unsafe fn keys<'
    assemble_whole_functions || return
    rejected '::keys, cannot prove' refine_whole_functions
}

reject_drop_loop() {
    mkdir -p drop-loop/verified
    collect_drop_bodies > drop-loop/verified/drop-bodies.rs || return
    rejected 'verified/drop-bodies.rs: patch does not apply' git -C drop-loop apply --check \
        --include=verified/drop-bodies.rs "$proof_dir/refinement.patch"
}

reject_operation() {
    local proof_diagnostic=$1 refinement_diagnostic=$2 signature=$3
    reject_proof "$proof_diagnostic" verified/insertion.rs "$signature"
    mv verified/operations.rs verified/operations-baseline.rs
    assemble_verified_operations || return
    rejected "$refinement_diagnostic" refine original/operations.rs verified/operations.rs
    mv verified/operations-baseline.rs verified/operations.rs
}

reject_merge_layout() {
    reject_operation 'No matching heap chunks: std::alloc::alloc_block_in' \
        'The constants FnDef std::alloc::Layout::new' '    unsafe fn do_merge_production<'
    assemble_whole_functions || return
    rejected 'The constants FnDef std::alloc::Layout::new' refine_whole_functions
}

reject_allocator_drop() {
    rustc +nightly-2026-09-25 --edition=2024 -Awarnings -Cpanic=unwind \
        verified/allocator-drop.rs -o allocator-drop
    ./allocator-drop > allocator-drop.log 2>&1
    reject_proof 'Cannot prove false' verified/allocator-drop.rs 'unsafe fn claimed_no_unwind<'
}

reject_root_callback() {
    project_root_callbacks "$library/alloc/src/collections/btree/map.rs" callers/entry.rs \
        original/operations-template.rs > callers/operations.rs
    rejected '::filter' refine callers/operations.rs verified/operations.rs
}

reject_unwind_order() {
    refine original/unwind_order.rs verified/unwind_order.rs
    rejected 'The two drop terminators drop different values' refine --check-unwind \
        original/unwind_order.rs verified/unwind_order.rs
}

reject_production_dispatch() {
    local btree="$library/alloc/src/collections/btree"
    mkdir -p dispatch/original
    copy_regions original/operations.rs.in original/node.rs original/borrow.rs \
        "$btree/map.rs" "$btree/map/entry.rs" > dispatch/original/operations.rs
    rejected 'patch does not apply' git -C dispatch apply --check \
        --include=original/operations.rs "$proof_dir/refinement.patch"
}

check_sources
assemble_views
check_ascend_body
assemble_loops
assemble_whole_functions
mkdir -p verifast/bin
cp -a -- "$verifast_home/bin/." verifast/bin/
git -C verifast apply --whitespace=error "$proof_dir/library-specs.patch"

if [[ ${1:-} == --negative ]]; then
    binary_mismatch='BinaryOp: The operators do not match'
    terminator_mismatch='in the original version refines the terminator of basic block'

    mkdir callers
    cp "$library/alloc/src/collections/btree/map/entry.rs" callers/entry.rs
    mutate allocator-drop-bound reject_allocator_drop
    mutate production-root-callback reject_root_callback
    mutate unwind-order reject_unwind_order
    mutate production-leaf-dispatch reject_production_dispatch
    mutate production-ascend rejected 'B-tree production ascend differs' check_ascend_body

    mutate whole-insert-loop reject_insert_loop
    mutate uninitialized-key-prefix reject_keys_prefix
    mutate write-shared-node-length reject_proof 'No matching heap chunks: points_to_<u16>' \
        verified/insertion.rs '    unsafe fn keys<'
    mutate duplicate-key-loan reject_proof 'No matching heap chunks: points_to<K>' \
        verified/insertion.rs '    unsafe fn kv_mut<'
    mutate invalid-parent-nonnull reject_proof 'Cannot prove !(get_pointer_address(null_pointer) = 0)' \
        verified/insertion.rs '    unsafe fn correct_parent_link(self)'
    assemble_whole_functions
    mutate wrong-merge-offset reject_proof 'Cannot prove condition' verified/insertion.rs \
        'unsafe fn finish_merge_tracking__VeriFast_wrapper<'
    mutate wrong-merge-offset reject_loop 'compare_merge_tracking_child_edge, at command'
    mutate wrong-left-steal-offset reject_loop "$binary_mismatch"

    mutate drop-value-guard rejected 'drop_key_val' refine_whole_functions
    mutate drop-next-pair rejected 'drop_kvs' refine_whole_functions
    mutate drop-loop-index reject_drop_loop
    mutate wrong-drop-slot reject_operation 'Cannot prove condition' 'project_drop_slots, cannot prove' \
        '    unsafe fn project_drop_slots<'
    mutate skipped-merge reject_operation 'No matching heap chunks: [_]merged_nodes' \
        'merge_tracking_child_edge, cannot prove that the terminator' '    unsafe fn merge_tracking_child_edge<'
    mutate skipped-stolen-edge reject_operation 'Cannot prove length(before) = get_std::ops::Range_start' \
        'are not equal' '    unsafe fn bulk_steal_left_production<'
    mutate bad-root-edge reject_operation 'Cannot prove condition' 'are not equal' \
        '    unsafe fn new_internal_production<'
    mutate root-guard rejected 'In function mem::replace, cannot prove' refine_whole_functions
    mutate bad-relink-read reject_proof 'Cannot prove condition' verified/relink.rs \
        '    unsafe fn correct_parent_link(self)'
    mutate bad-suffix-range reject_operation 'No matching heap chunks: edges_range_loan' \
        'move_suffix_production, cannot prove that statement' '    unsafe fn move_suffix_production<'
    mutate bad-separator reject_proof 'No matching heap chunks: keys_slot_loan' verified/insertion.rs \
        'unsafe fn merge_keys<'
    mutate bad-split-boundaries reject_operation 'No matching heap chunks: array<std::mem::MaybeUninit<V>>' \
        'cannot prove that the terminator of basic block' '    unsafe fn split_leaf_data<'
    mutate missing-internal-relink reject_operation 'No matching heap chunks: linked_headers' \
        "$terminator_mismatch" '    unsafe fn from_new_internal<'
    mutate short-edges reject_operation \
        'No matching heap chunks: array<std::mem::MaybeUninit<std::ptr::NonNull<LeafNode<K, V>>>>' \
        "$terminator_mismatch" '    unsafe fn split_production_internal<'
    mutate bad-leaf-capacity reject_operation 'Cannot prove len < CAPACITY' "$binary_mismatch" \
        '    unsafe fn insert_leaf_production<'
    mutate bad-internal-capacity reject_operation 'Cannot prove len < CAPACITY' "$binary_mismatch" \
        '    unsafe fn insert_production<'
    mutate missing-insert-relink reject_operation 'Cannot prove length(before) = get_std::ops::Range_start' \
        'are not equal' '    unsafe fn insert_fit_production<'
    mutate wrong-layout reject_merge_layout
    mutate bad-key-range rejected 'are not equal: Symbol' refine original/operations.rs verified/operations.rs
    mutate production-steal-range rejected 'B-tree production snapshot changed: node.rs' check_sources
    exit 0
fi

verify_proof "$verifast_home/bin/verifast" -skip_specless_fns verified/backlinks.rs
"$verifast_home/bin/refinement-checker" original/backlinks.rs verified/backlinks.rs
# Rust MIR retains assertion failures and cleanup blocks proved unreachable.
verify_proof proof verified/insertion.rs
verify_proof proof verified/relink.rs
refine original/operations.rs verified/operations.rs
refine_whole_functions
refine original/loops/main.rs verified/loops/main.rs
verify_proof proof verified/root_replace.rs
