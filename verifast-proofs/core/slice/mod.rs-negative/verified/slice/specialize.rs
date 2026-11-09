
pub trait SpecFill<T> {
    fn spec_fill(&mut self, val: T);
}
impl<T: Clone> SpecFill<T> for [T] {
    fn spec_fill(&mut self, _val: T) { loop {} }
}
