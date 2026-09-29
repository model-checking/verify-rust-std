#![crate_type = "lib"]
#![crate_name = "const_refinement"]

pub fn width<const N: usize, const M: usize>() -> usize {
    M
}
