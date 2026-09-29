#![crate_type = "lib"]
#![crate_name = "const_refinement"]

pub fn width<const A: usize, const B: usize>() -> usize {
    A
}
