#[flux::defs {
    property ShiftRightByFour[>>](x, y) {
        16 * [>>](x, 4) == x
    }

    property MaskBy15[&](x, y) {
        [&](x, y) <= y
    }
}]
const _: () = {};