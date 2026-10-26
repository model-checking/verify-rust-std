
pub trait SliceContains<T> {
    fn slice_contains(&self, x: &[T]) -> bool;
}
impl<T: PartialEq> SliceContains<T> for T {
    fn slice_contains(&self, _x: &[T]) -> bool { loop {} }
}
