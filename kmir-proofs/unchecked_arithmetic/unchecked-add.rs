
fn main() {
    let a:i16 = 42;
    let b:i16 = -43;
    
    let result = unchecked_op(a, b);

    assert!((a + b < i16::MAX) && (a + b > i16::MIN));
}

fn unchecked_op(a: i16, b: i16) -> i16 {
    let unchecked_res = unsafe { a.unchecked_add(b) };
    unchecked_res
}
