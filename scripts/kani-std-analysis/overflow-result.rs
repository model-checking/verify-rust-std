// Check both fields of the arithmetic tuples affected by CBMC issue #9145.
// Widened arithmetic supplies an independent result and overflow predicate.
#[kani::proof]
fn signed_add_subtract() {
    let lhs: i16 = kani::any();
    let rhs: i16 = kani::any();
    let sum = i32::from(lhs) + i32::from(rhs);
    let difference = i32::from(lhs) - i32::from(rhs);
    let bounds = i32::from(i16::MIN)..=i32::from(i16::MAX);
    assert_eq!(
        lhs.overflowing_add(rhs),
        (sum as i16, !bounds.contains(&sum))
    );
    assert_eq!(
        lhs.overflowing_sub(rhs),
        (difference as i16, !bounds.contains(&difference))
    );
    kani::cover(
        !bounds.contains(&sum),
        "addition overflow remains reachable",
    );
    kani::cover(
        !bounds.contains(&difference),
        "subtraction overflow remains reachable",
    );
}

#[kani::proof]
fn signed_multiply() {
    let lhs: i8 = kani::any();
    let rhs: i8 = kani::any();
    let product = i16::from(lhs) * i16::from(rhs);
    let overflow = !(i16::from(i8::MIN)..=i16::from(i8::MAX)).contains(&product);
    assert_eq!(lhs.overflowing_mul(rhs), (product as i8, overflow));
    kani::cover(overflow, "signed multiplication overflow remains reachable");
}

#[kani::proof]
fn unsigned_multiply() {
    let lhs: u8 = kani::any();
    let rhs: u8 = kani::any();
    let product = u16::from(lhs) * u16::from(rhs);
    let overflow = product > u16::from(u8::MAX);
    assert_eq!(lhs.overflowing_mul(rhs), (product as u8, overflow));
    kani::cover(
        overflow,
        "unsigned multiplication overflow remains reachable",
    );
}
