// @kmir prove-rs: unchecked_add_i32 unchecked_sub_usize unchecked_mul_isize

fn main() {
    unchecked_add_i32(1,2);
    unchecked_sub_usize(1, 2);
    unchecked_mul_isize(1, 2);
}

/// If the precondition is not met, the program is not executed (exits cleanly, ex falso quodlibet)
macro_rules! precondition {
    ($pre:expr, $block:expr) => {
        if $pre { $block }
    };
}

/////////////////////////////////////////////////////////////////////

fn unchecked_add_i32(a: i32, b: i32) {

    precondition!(
        ((a as i64 + b as i64) <= i32::MAX as i64) &&
        ( a as i64 + b as i64  >= i32::MIN as i64),
        // =========================================
         unsafe {
            let result = a.unchecked_add(b);
            assert!(result as i64 == a as i64 + b as i64)
        }
    );
}


macro_rules! unchecked_add_claim_for {
    ($name:ident, $ty:ident) => {
        #[allow(unused)]
        fn $name(a: $ty, b: $ty)
        {
            use std::$ty;
            precondition!(
                ((a as i128 + b as i128) <= $ty::MAX as i128) &&
                ( a as i128 + b as i128  >= $ty::MIN as i128),
                // =========================================
                 unsafe {
                    let result = a.unchecked_add(b);
                    assert!(result as i128 == a as i128 + b as i128)
                }
            );
        }
    }
}

unchecked_add_claim_for!(unchecked_add_i8   , i8   );
unchecked_add_claim_for!(unchecked_add_i16  , i16  );
// unchecked_add_claim_for!(unchecked_add_i32  , i32  ); // already above
unchecked_add_claim_for!(unchecked_add_i64  , i64  );
unchecked_add_claim_for!(unchecked_add_isize, isize);
unchecked_add_claim_for!(unchecked_add_u8   , u8   );
unchecked_add_claim_for!(unchecked_add_u16  , u16  );
unchecked_add_claim_for!(unchecked_add_u32  , u32  );
unchecked_add_claim_for!(unchecked_add_u64  , u64  );
unchecked_add_claim_for!(unchecked_add_usize, usize);

/////////////////////////////////////////////////////////////////////

macro_rules! unchecked_sub_claim_for {
    ($name:ident, $ty:ident) => {
        #[allow(unused)]
        fn $name(a: $ty, b: $ty)
        {
            use std::$ty;
            precondition!(
                ((a as i128 - b as i128) <= $ty::MAX as i128) &&
                ( a as i128 - b as i128  >= $ty::MIN as i128),
                // =========================================
                 unsafe {
                    let result = a.unchecked_sub(b);
                    assert!(result as i128 == a as i128 - b as i128)
                }
            );
        }
    }
}

unchecked_sub_claim_for!(unchecked_sub_i8   , i8   );
unchecked_sub_claim_for!(unchecked_sub_i16  , i16  );
unchecked_sub_claim_for!(unchecked_sub_i32  , i32  );
unchecked_sub_claim_for!(unchecked_sub_i64  , i64  );
unchecked_sub_claim_for!(unchecked_sub_isize, isize);
unchecked_sub_claim_for!(unchecked_sub_u8   , u8   );
unchecked_sub_claim_for!(unchecked_sub_u16  , u16  );
unchecked_sub_claim_for!(unchecked_sub_u32  , u32  );
unchecked_sub_claim_for!(unchecked_sub_u64  , u64  );
unchecked_sub_claim_for!(unchecked_sub_usize, usize);

/////////////////////////////////////////////////////////////////////

macro_rules! unchecked_mul_claim_for {
    ($name:ident, $ty:ident) => {
        #[allow(unused)]
        fn $name(a: $ty, b: $ty)
        {
            use std::$ty;
            precondition!(
                ((a as i128 * b as i128) <= $ty::MAX as i128) &&
                ( a as i128 * b as i128  >= $ty::MIN as i128),
                // =========================================
                    unsafe {
                    let result = a.unchecked_mul(b);
                    assert!(result as i128 == a as i128 * b as i128)
                }
            );
        }
    }
}

unchecked_mul_claim_for!(unchecked_mul_i8   , i8   );
unchecked_mul_claim_for!(unchecked_mul_i16  , i16  );
unchecked_mul_claim_for!(unchecked_mul_i32  , i32  );
unchecked_mul_claim_for!(unchecked_mul_i64  , i64  );
unchecked_mul_claim_for!(unchecked_mul_isize, isize);
unchecked_mul_claim_for!(unchecked_mul_u8   , u8   );
unchecked_mul_claim_for!(unchecked_mul_u16  , u16  );
unchecked_mul_claim_for!(unchecked_mul_u32  , u32  );
// insufficient bit size for precondition
// unchecked_mul_claim_for!(unchecked_mul_u64  , u64  );
// unchecked_mul_claim_for!(unchecked_mul_usize, usize);
