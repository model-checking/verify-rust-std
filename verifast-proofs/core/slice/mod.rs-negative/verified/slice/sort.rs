
pub mod select {
    pub fn partition_at_index<T, F>(_v: &mut [T], _index: usize, _is_less: F) -> (&mut [T], &mut T, &mut [T])
    where F: FnMut(&T, &T) -> bool { loop {} }
}
pub mod unstable {
    pub fn sort<T, F>(_v: &mut [T], _is_less: &mut F)
    where F: FnMut(&T, &T) -> bool { loop {} }
    pub fn partial_sort<T, R, F>(_v: &mut [T], _range: R, _is_less: F)
    where R: core::ops::RangeBounds<usize>, F: FnMut(&T, &T) -> bool { loop {} }
}
