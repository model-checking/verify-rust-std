//! This file contains auxiliary definitions for Flux

/// List of properties tracked for the result of primitive bitwise operations.
/// See the following link for more information on how extensible properties for primitive operations work:
/// <https://flux-rs.github.io/flux/guide/specifications.html#extensible-properties-for-primitive-ops>
#[flux::defs {
    property ShiftRightByFour[>>](x, y) {
        16 * [>>](x, 4) == x
    }

    property MaskBy15[&](x, y) {
        [&](x, y) <= y
    }
}]
const _: () = {};
