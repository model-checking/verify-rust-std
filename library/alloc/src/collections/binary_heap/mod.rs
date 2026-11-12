//! A priority queue implemented with a binary heap.
//!
//! Insertion and popping the largest element have *O*(log(*n*)) time complexity.
//! Checking the largest element is *O*(1). Converting a vector to a binary heap
//! can be done in-place, and has *O*(*n*) complexity. A binary heap can also be
//! converted to a sorted vector in-place, allowing it to be used for an *O*(*n* * log(*n*))
//! in-place heapsort.
//!
//! # Examples
//!
//! This is a larger example that implements [Dijkstra's algorithm][dijkstra]
//! to solve the [shortest path problem][sssp] on a [directed graph][dir_graph].
//! It shows how to use [`BinaryHeap`] with custom types.
//!
//! [dijkstra]: https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
//! [sssp]: https://en.wikipedia.org/wiki/Shortest_path_problem
//! [dir_graph]: https://en.wikipedia.org/wiki/Directed_graph
//!
//! ```
//! use std::cmp::Ordering;
//! use std::collections::BinaryHeap;
//!
//! #[derive(Copy, Clone, Eq, PartialEq)]
//! struct State {
//!     cost: usize,
//!     position: usize,
//! }
//!
//! // The priority queue depends on `Ord`.
//! // Explicitly implement the trait so the queue becomes a min-heap
//! // instead of a max-heap.
//! impl Ord for State {
//!     fn cmp(&self, other: &Self) -> Ordering {
//!         // Notice that we flip the ordering on costs.
//!         // In case of a tie we compare positions - this step is necessary
//!         // to make implementations of `PartialEq` and `Ord` consistent.
//!         other.cost.cmp(&self.cost)
//!             .then_with(|| self.position.cmp(&other.position))
//!     }
//! }
//!
//! // `PartialOrd` needs to be implemented as well.
//! impl PartialOrd for State {
//!     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
//!         Some(self.cmp(other))
//!     }
//! }
//!
//! // Each node is represented as a `usize`, for a shorter implementation.
//! struct Edge {
//!     node: usize,
//!     cost: usize,
//! }
//!
//! // Dijkstra's shortest path algorithm.
//!
//! // Start at `start` and use `dist` to track the current shortest distance
//! // to each node. This implementation isn't memory-efficient as it may leave duplicate
//! // nodes in the queue. It also uses `usize::MAX` as a sentinel value,
//! // for a simpler implementation.
//! fn shortest_path(adj_list: &Vec<Vec<Edge>>, start: usize, goal: usize) -> Option<usize> {
//!     // dist[node] = current shortest distance from `start` to `node`
//!     let mut dist: Vec<_> = (0..adj_list.len()).map(|_| usize::MAX).collect();
//!
//!     let mut heap = BinaryHeap::new();
//!
//!     // We're at `start`, with a zero cost
//!     dist[start] = 0;
//!     heap.push(State { cost: 0, position: start });
//!
//!     // Examine the frontier with lower cost nodes first (min-heap)
//!     while let Some(State { cost, position }) = heap.pop() {
//!         // Alternatively we could have continued to find all shortest paths
//!         if position == goal { return Some(cost); }
//!
//!         // Important as we may have already found a better way
//!         if cost > dist[position] { continue; }
//!
//!         // For each node we can reach, see if we can find a way with
//!         // a lower cost going through this node
//!         for edge in &adj_list[position] {
//!             let next = State { cost: cost + edge.cost, position: edge.node };
//!
//!             // If so, add it to the frontier and continue
//!             if next.cost < dist[next.position] {
//!                 heap.push(next);
//!                 // Relaxation, we have now found a better way
//!                 dist[next.position] = next.cost;
//!             }
//!         }
//!     }
//!
//!     // Goal not reachable
//!     None
//! }
//!
//! fn main() {
//!     // This is the directed graph we're going to use.
//!     // The node numbers correspond to the different states,
//!     // and the edge weights symbolize the cost of moving
//!     // from one node to another.
//!     // Note that the edges are one-way.
//!     //
//!     //                  7
//!     //          +-----------------+
//!     //          |                 |
//!     //          v   1        2    |  2
//!     //          0 -----> 1 -----> 3 ---> 4
//!     //          |        ^        ^      ^
//!     //          |        | 1      |      |
//!     //          |        |        | 3    | 1
//!     //          +------> 2 -------+      |
//!     //           10      |               |
//!     //                   +---------------+
//!     //
//!     // The graph is represented as an adjacency list where each index,
//!     // corresponding to a node value, has a list of outgoing edges.
//!     // Chosen for its efficiency.
//!     let graph = vec![
//!         // Node 0
//!         vec![Edge { node: 2, cost: 10 },
//!              Edge { node: 1, cost: 1 }],
//!         // Node 1
//!         vec![Edge { node: 3, cost: 2 }],
//!         // Node 2
//!         vec![Edge { node: 1, cost: 1 },
//!              Edge { node: 3, cost: 3 },
//!              Edge { node: 4, cost: 1 }],
//!         // Node 3
//!         vec![Edge { node: 0, cost: 7 },
//!              Edge { node: 4, cost: 2 }],
//!         // Node 4
//!         vec![]];
//!
//!     assert_eq!(shortest_path(&graph, 0, 1), Some(1));
//!     assert_eq!(shortest_path(&graph, 0, 3), Some(3));
//!     assert_eq!(shortest_path(&graph, 3, 0), Some(7));
//!     assert_eq!(shortest_path(&graph, 0, 4), Some(5));
//!     assert_eq!(shortest_path(&graph, 4, 0), None);
//! }
//! ```

#![allow(missing_docs)]
#![stable(feature = "rust1", since = "1.0.0")]

use core::alloc::Allocator;
use core::iter::{FusedIterator, InPlaceIterable, SourceIter, TrustedFused, TrustedLen};
#[cfg(kani)]
use core::kani;
use core::mem::{self, ManuallyDrop, swap};
use core::num::NonZero;
use core::ops::{Deref, DerefMut};
use core::{fmt, ptr};

use safety::{ensures, requires};

use crate::alloc::{AllocatorNightly, Global};
use crate::collections::TryReserveError;
use crate::slice;
#[cfg(not(test))]
use crate::vec::AsVecIntoIter;
use crate::vec::{self, Vec};

/// A priority queue implemented with a binary heap.
///
/// This will be a max-heap.
///
/// It is a logic error for an item to be modified in such a way that the
/// item's ordering relative to any other item, as determined by the [`Ord`]
/// trait, changes while it is in the heap. This is normally only possible
/// through interior mutability, global state, I/O, or unsafe code. The
/// behavior resulting from such a logic error is not specified, but will
/// be encapsulated to the `BinaryHeap` that observed the logic error and not
/// result in undefined behavior. This could include panics, incorrect results,
/// aborts, memory leaks, and non-termination.
///
/// As long as no elements change their relative order while being in the heap
/// as described above, the API of `BinaryHeap` guarantees that the heap
/// invariant remains intact i.e. its methods all behave as documented. For
/// example if a method is documented as iterating in sorted order, that's
/// guaranteed to work as long as elements in the heap have not changed order,
/// even in the presence of closures getting unwinded out of, iterators getting
/// leaked, and similar foolishness.
///
/// # Examples
///
/// ```
/// use std::collections::BinaryHeap;
///
/// // Type inference lets us omit an explicit type signature (which
/// // would be `BinaryHeap<i32>` in this example).
/// let mut heap = BinaryHeap::new();
///
/// // We can use peek to look at the next item in the heap. In this case,
/// // there's no items in there yet so we get None.
/// assert_eq!(heap.peek(), None);
///
/// // Let's add some scores...
/// heap.push(1);
/// heap.push(5);
/// heap.push(2);
///
/// // Now peek shows the most important item in the heap.
/// assert_eq!(heap.peek(), Some(&5));
///
/// // We can check the length of a heap.
/// assert_eq!(heap.len(), 3);
///
/// // We can iterate over the items in the heap, although they are returned in
/// // a random order.
/// for x in &heap {
///     println!("{x}");
/// }
///
/// // If we instead pop these scores, they should come back in order.
/// assert_eq!(heap.pop(), Some(5));
/// assert_eq!(heap.pop(), Some(2));
/// assert_eq!(heap.pop(), Some(1));
/// assert_eq!(heap.pop(), None);
///
/// // We can clear the heap of any remaining items.
/// heap.clear();
///
/// // The heap should now be empty.
/// assert!(heap.is_empty())
/// ```
///
/// A `BinaryHeap` with a known list of items can be initialized from an array:
///
/// ```
/// use std::collections::BinaryHeap;
///
/// let heap = BinaryHeap::from([1, 5, 2]);
/// ```
///
/// ## Min-heap
///
/// Either [`core::cmp::Reverse`] or a custom [`Ord`] implementation can be used to
/// make `BinaryHeap` a min-heap. This makes `heap.pop()` return the smallest
/// value instead of the greatest one.
///
/// ```
/// use std::collections::BinaryHeap;
/// use std::cmp::Reverse;
///
/// let mut heap = BinaryHeap::new();
///
/// // Wrap values in `Reverse`
/// heap.push(Reverse(1));
/// heap.push(Reverse(5));
/// heap.push(Reverse(2));
///
/// // If we pop these scores now, they should come back in the reverse order.
/// assert_eq!(heap.pop(), Some(Reverse(1)));
/// assert_eq!(heap.pop(), Some(Reverse(2)));
/// assert_eq!(heap.pop(), Some(Reverse(5)));
/// assert_eq!(heap.pop(), None);
/// ```
///
/// # Time complexity
///
/// | [push]  | [pop]         | [peek]/[peek\_mut] |
/// |---------|---------------|--------------------|
/// | *O*(1)~ | *O*(log(*n*)) | *O*(1)             |
///
/// The value for `push` is an expected cost; the method documentation gives a
/// more detailed analysis.
///
/// [`core::cmp::Reverse`]: core::cmp::Reverse
/// [`Cell`]: core::cell::Cell
/// [`RefCell`]: core::cell::RefCell
/// [push]: BinaryHeap::push
/// [pop]: BinaryHeap::pop
/// [peek]: BinaryHeap::peek
/// [peek\_mut]: BinaryHeap::peek_mut
#[stable(feature = "rust1", since = "1.0.0")]
#[cfg_attr(not(test), rustc_diagnostic_item = "BinaryHeap")]
pub struct BinaryHeap<
    T,
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")] A: Allocator = Global,
> {
    data: Vec<T, A>,
}

/// Structure wrapping a mutable reference to the greatest item on a
/// `BinaryHeap`.
///
/// This `struct` is created by the [`peek_mut`] method on [`BinaryHeap`]. See
/// its documentation for more.
///
/// [`peek_mut`]: BinaryHeap::peek_mut
#[stable(feature = "binary_heap_peek_mut", since = "1.12.0")]
pub struct PeekMut<
    'a,
    T: 'a + Ord,
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")] A: Allocator = Global,
> {
    heap: &'a mut BinaryHeap<T, A>,
    // If a set_len + sift_down are required, this is Some. If a &mut T has not
    // yet been exposed to peek_mut()'s caller, it's None.
    original_len: Option<NonZero<usize>>,
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl<T: Ord + fmt::Debug, A: Allocator> fmt::Debug for PeekMut<'_, T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PeekMut").field(&self.heap.data[0]).finish()
    }
}

#[stable(feature = "binary_heap_peek_mut", since = "1.12.0")]
impl<T: Ord, A: Allocator> Drop for PeekMut<'_, T, A> {
    fn drop(&mut self) {
        if let Some(original_len) = self.original_len {
            // SAFETY: That's how many elements were in the Vec at the time of
            // the PeekMut::deref_mut call, and therefore also at the time of
            // the BinaryHeap::peek_mut call. Since the PeekMut did not end up
            // getting leaked, we are now undoing the leak amplification that
            // the DerefMut prepared for.
            unsafe { self.heap.data.set_len(original_len.get()) };

            // SAFETY: PeekMut is only instantiated for non-empty heaps.
            unsafe { self.heap.sift_down(0) };
        }
    }
}

#[stable(feature = "binary_heap_peek_mut", since = "1.12.0")]
impl<T: Ord, A: Allocator> Deref for PeekMut<'_, T, A> {
    type Target = T;
    fn deref(&self) -> &T {
        debug_assert!(!self.heap.is_empty());
        // SAFETY: PeekMut is only instantiated for non-empty heaps
        unsafe { self.heap.data.get_unchecked(0) }
    }
}

#[stable(feature = "binary_heap_peek_mut", since = "1.12.0")]
impl<T: Ord, A: Allocator> DerefMut for PeekMut<'_, T, A> {
    fn deref_mut(&mut self) -> &mut T {
        debug_assert!(!self.heap.is_empty());

        let len = self.heap.len();
        if len > 1 {
            // Here we preemptively leak all the rest of the underlying vector
            // after the currently max element. If the caller mutates the &mut T
            // we're about to give them, and then leaks the PeekMut, all these
            // elements will remain leaked. If they don't leak the PeekMut, then
            // either Drop or PeekMut::pop will un-leak the vector elements.
            //
            // This is technique is described throughout several other places in
            // the standard library as "leak amplification".
            // SAFETY: len > 1 so len != 0.
            self.original_len = Some(unsafe { NonZero::new_unchecked(len) });
            // SAFETY: len > 1 so all this does for now is leak elements,
            // which is safe.
            unsafe { self.heap.data.set_len(1) };
        }

        // SAFETY: PeekMut is only instantiated for non-empty heaps
        unsafe { self.heap.data.get_unchecked_mut(0) }
    }
}

impl<'a, T: Ord, A: Allocator> PeekMut<'a, T, A> {
    /// Sifts the current element to its new position.
    ///
    /// Afterwards refers to the new element. Returns if the element changed.
    ///
    /// ## Examples
    ///
    /// The condition can be used to upper bound all elements in the heap. When only few elements
    /// are affected, the heap's sort ensures this is faster than a reconstruction from the raw
    /// element list and requires no additional allocation.
    ///
    /// ```
    /// #![feature(binary_heap_peek_mut_refresh)]
    /// use std::collections::BinaryHeap;
    ///
    /// let mut heap: BinaryHeap<u32> = (0..128).collect();
    /// let mut peek = heap.peek_mut().unwrap();
    ///
    /// loop {
    ///     *peek = 99;
    ///
    ///     if !peek.refresh() {
    ///         break;
    ///     }
    /// }
    ///
    /// // Post condition, this is now an upper bound.
    /// assert!(*peek < 100);
    /// ```
    ///
    /// When the element remains the maximum after modification, the peek remains unchanged:
    ///
    /// ```
    /// #![feature(binary_heap_peek_mut_refresh)]
    /// use std::collections::BinaryHeap;
    ///
    /// let mut heap: BinaryHeap<u32> = [1, 2, 3].into();
    /// let mut peek = heap.peek_mut().unwrap();
    ///
    /// assert_eq!(*peek, 3);
    /// *peek = 42;
    ///
    /// // When we refresh, the peek is updated to the new maximum.
    /// assert!(!peek.refresh(), "42 is even larger than 3");
    /// assert_eq!(*peek, 42);
    /// ```
    #[unstable(feature = "binary_heap_peek_mut_refresh", issue = "138355")]
    #[must_use = "is equivalent to dropping and getting a new PeekMut except for return information"]
    pub fn refresh(&mut self) -> bool {
        // The length of the underlying heap is unchanged by sifting down. The value stored for leak
        // amplification thus remains accurate. We erase the leak amplification firstly because the
        // operation is then equivalent to constructing a new PeekMut and secondly this avoids any
        // future complication where original_len being non-empty would be interpreted as the heap
        // having been leak amplified instead of checking the heap itself.
        if let Some(original_len) = self.original_len.take() {
            // SAFETY: This is how many elements were in the Vec at the time of
            // the BinaryHeap::peek_mut call.
            unsafe { self.heap.data.set_len(original_len.get()) };

            // The length of the heap did not change by sifting, upholding our own invariants.

            // SAFETY: PeekMut is only instantiated for non-empty heaps.
            (unsafe { self.heap.sift_down(0) }) != 0
        } else {
            // The element was not modified.
            false
        }
    }

    /// Removes the peeked value from the heap and returns it.
    #[stable(feature = "binary_heap_peek_mut_pop", since = "1.18.0")]
    pub fn pop(mut this: PeekMut<'a, T, A>) -> T {
        if let Some(original_len) = this.original_len.take() {
            // SAFETY: This is how many elements were in the Vec at the time of
            // the BinaryHeap::peek_mut call.
            unsafe { this.heap.data.set_len(original_len.get()) };

            // Unlike in Drop, here we don't also need to do a sift_down even if
            // the caller could've mutated the element. It is removed from the
            // heap on the next line and pop() is not sensitive to its value.
        }

        // SAFETY: Have a `PeekMut` element proves that the associated binary heap being non-empty,
        // so the `pop` operation will not fail.
        unsafe { this.heap.pop().unwrap_unchecked() }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Clone, A: Allocator + Clone> Clone for BinaryHeap<T, A> {
    fn clone(&self) -> Self {
        BinaryHeap { data: self.data.clone() }
    }

    /// Overwrites the contents of `self` with a clone of the contents of `source`.
    ///
    /// This method is preferred over simply assigning `source.clone()` to `self`,
    /// as it avoids reallocation if possible.
    ///
    /// See [`Vec::clone_from()`] for more details.
    fn clone_from(&mut self, source: &Self) {
        self.data.clone_from(&source.data);
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> Default for BinaryHeap<T> {
    /// Creates an empty `BinaryHeap<T>`.
    #[inline]
    fn default() -> BinaryHeap<T> {
        BinaryHeap::new()
    }
}

#[stable(feature = "binaryheap_debug", since = "1.4.0")]
impl<T: fmt::Debug, A: Allocator> fmt::Debug for BinaryHeap<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

struct RebuildOnDrop<
    'a,
    T: Ord,
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")] A: Allocator = Global,
> {
    heap: &'a mut BinaryHeap<T, A>,
    rebuild_from: usize,
}

impl<T: Ord, A: Allocator> Drop for RebuildOnDrop<'_, T, A> {
    fn drop(&mut self) {
        self.heap.rebuild_tail(self.rebuild_from);
    }
}

impl<T> BinaryHeap<T> {
    /// Creates an empty `BinaryHeap` as a max-heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::new();
    /// heap.push(4);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_binary_heap_constructor", since = "1.80.0")]
    #[must_use]
    pub const fn new() -> BinaryHeap<T> {
        BinaryHeap { data: vec![] }
    }

    /// Creates an empty `BinaryHeap` with at least the specified capacity.
    ///
    /// The binary heap will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is zero, the binary heap will not allocate.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::with_capacity(10);
    /// heap.push(4);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> BinaryHeap<T> {
        BinaryHeap { data: Vec::with_capacity(capacity) }
    }
}

impl<T, A: Allocator> BinaryHeap<T, A> {
    /// Creates an empty `BinaryHeap` as a max-heap, using `A` as allocator.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(allocator_ext)]
    ///
    /// use std::alloc::System;
    /// use std::collections::BinaryHeap;
    ///
    /// let heap : BinaryHeap<i32, System> = BinaryHeap::new_in(System);
    /// ```
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")]
    #[rustc_const_unstable(feature = "allocator_ext", issue = "163177")]
    #[must_use]
    pub const fn new_in(alloc: A) -> BinaryHeap<T, A> {
        BinaryHeap { data: Vec::new_in(alloc) }
    }

    /// Creates an empty `BinaryHeap` with at least the specified capacity, using `A` as allocator.
    ///
    /// The binary heap will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is zero, the binary heap will not allocate.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(allocator_ext)]
    ///
    /// use std::alloc::System;
    /// use std::collections::BinaryHeap;
    ///
    /// let heap: BinaryHeap<i32, System> = BinaryHeap::with_capacity_in(10, System);
    /// ```
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")]
    #[must_use]
    pub fn with_capacity_in(capacity: usize, alloc: A) -> BinaryHeap<T, A> {
        BinaryHeap { data: Vec::with_capacity_in(capacity, alloc) }
    }

    /// Creates a `BinaryHeap` using the supplied `vec`. This does not rebuild the heap,
    /// so `vec` must already be a max-heap.
    ///
    /// # Safety
    ///
    /// The supplied `vec` must be a max-heap, i.e. for all indices `0 < i < vec.len()`,
    /// `vec[(i - 1) / 2] >= vec[i]`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(binary_heap_from_raw_vec)]
    ///
    /// use std::collections::BinaryHeap;
    /// let heap = BinaryHeap::from([1, 2, 3]);
    /// let vec = heap.into_vec();
    ///
    /// // Safety: vec is the output of heap.from_vec(), so is a max-heap.
    /// let mut new_heap = unsafe {
    ///     BinaryHeap::from_raw_vec(vec)
    /// };
    /// assert_eq!(new_heap.pop(), Some(3));
    /// assert_eq!(new_heap.pop(), Some(2));
    /// assert_eq!(new_heap.pop(), Some(1));
    /// assert_eq!(new_heap.pop(), None);
    /// ```
    #[unstable(feature = "binary_heap_from_raw_vec", issue = "152500")]
    #[must_use]
    pub unsafe fn from_raw_vec(vec: Vec<T, A>) -> BinaryHeap<T, A> {
        BinaryHeap { data: vec }
    }
}

impl<T: Ord, A: Allocator> BinaryHeap<T, A> {
    /// Returns a mutable reference to the greatest item in the binary heap, or
    /// `None` if it is empty.
    ///
    /// Note: If the `PeekMut` value is leaked, some heap elements might get
    /// leaked along with it, but the remaining elements will remain a valid
    /// heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::new();
    /// assert!(heap.peek_mut().is_none());
    ///
    /// heap.push(1);
    /// heap.push(5);
    /// heap.push(2);
    /// if let Some(mut val) = heap.peek_mut() {
    ///     *val = 0;
    /// }
    /// assert_eq!(heap.peek(), Some(&2));
    /// ```
    ///
    /// # Time complexity
    ///
    /// If the item is modified then the worst case time complexity is *O*(log(*n*)),
    /// otherwise it's *O*(1).
    #[stable(feature = "binary_heap_peek_mut", since = "1.12.0")]
    pub fn peek_mut(&mut self) -> Option<PeekMut<'_, T, A>> {
        if self.is_empty() { None } else { Some(PeekMut { heap: self, original_len: None }) }
    }

    /// Removes the greatest item from the binary heap and returns it, or `None` if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::from([1, 3]);
    ///
    /// assert_eq!(heap.pop(), Some(3));
    /// assert_eq!(heap.pop(), Some(1));
    /// assert_eq!(heap.pop(), None);
    /// ```
    ///
    /// # Time complexity
    ///
    /// The worst case cost of `pop` on a heap containing *n* elements is *O*(log(*n*)).
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pop(&mut self) -> Option<T> {
        self.data.pop().map(|mut item| {
            if !self.is_empty() {
                swap(&mut item, &mut self.data[0]);
                // SAFETY: !self.is_empty() means that self.len() > 0
                unsafe { self.sift_down_to_bottom(0) };
            }
            item
        })
    }

    /// Removes and returns the greatest item from the binary heap if the predicate
    /// returns `true`, or [`None`] if the predicate returns false or the heap
    /// is empty (the predicate will not be called in that case).
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(binary_heap_pop_if)]
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::from([1, 2]);
    /// let pred = |x: &i32| *x % 2 == 0;
    ///
    /// assert_eq!(heap.pop_if(pred), Some(2));
    /// assert_eq!(heap.as_slice(), [1]);
    /// assert_eq!(heap.pop_if(pred), None);
    /// assert_eq!(heap.as_slice(), [1]);
    /// ```
    ///
    /// # Time complexity
    ///
    /// The worst case cost of `pop_if` on a heap containing *n* elements is *O*(log(*n*)).
    #[unstable(feature = "binary_heap_pop_if", issue = "151828")]
    pub fn pop_if(&mut self, predicate: impl FnOnce(&T) -> bool) -> Option<T> {
        let first = self.peek()?;
        if predicate(first) { self.pop() } else { None }
    }

    /// Pushes an item onto the binary heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::new();
    /// heap.push(3);
    /// heap.push(5);
    /// heap.push(1);
    ///
    /// assert_eq!(heap.len(), 3);
    /// assert_eq!(heap.peek(), Some(&5));
    /// ```
    ///
    /// # Time complexity
    ///
    /// The expected cost of `push`, averaged over every possible ordering of
    /// the elements being pushed, and over a sufficiently large number of
    /// pushes, is *O*(1). This is the most meaningful cost metric when pushing
    /// elements that are *not* already in any sorted pattern.
    ///
    /// The time complexity degrades if elements are pushed in predominantly
    /// ascending order. In the worst case, elements are pushed in ascending
    /// sorted order and the amortized cost per push is *O*(log(*n*)) against a heap
    /// containing *n* elements.
    ///
    /// The worst case cost of a *single* call to `push` is *O*(*n*). The worst case
    /// occurs when capacity is exhausted and needs a resize. The resize cost
    /// has been amortized in the previous figures.
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("append", "put")]
    pub fn push(&mut self, item: T) {
        let old_len = self.len();
        self.data.push(item);
        // SAFETY: Since we pushed a new item it means that
        //  old_len = self.len() - 1 < self.len()
        unsafe { self.sift_up(0, old_len) };
    }

    /// Consumes the `BinaryHeap` and returns a vector in sorted
    /// (ascending) order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::from([1, 2, 4, 5, 7]);
    /// heap.push(6);
    /// heap.push(3);
    ///
    /// let vec = heap.into_sorted_vec();
    /// assert_eq!(vec, [1, 2, 3, 4, 5, 6, 7]);
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "binary_heap_extras_15", since = "1.5.0")]
    pub fn into_sorted_vec(mut self) -> Vec<T, A> {
        let mut end = self.len();
        #[cfg_attr(kani, kani::loop_invariant(end <= self.data.len()))]
        #[cfg_attr(kani, kani::loop_modifies(&end, self.kani_slice()))]
        #[cfg_attr(kani, kani::loop_decreases(end))]
        while end > 1 {
            end -= 1;
            // SAFETY: `end` goes from `self.len() - 1` to 1 (both included),
            //  so it's always a valid index to access.
            //  It is safe to access index 0 (i.e. `ptr`), because
            //  1 <= end < self.len(), which means self.len() >= 2.
            unsafe {
                let ptr = self.data.as_mut_ptr();
                ptr::swap(ptr, ptr.add(end));
            }
            // SAFETY: `end` goes from `self.len() - 1` to 1 (both included) so:
            //  0 < 1 <= end <= self.len() - 1 < self.len()
            //  Which means 0 < end and end < self.len().
            unsafe { self.sift_down_range(0, end) };
        }
        self.into_vec()
    }

    // The implementations of sift_up and sift_down use unsafe blocks in
    // order to move an element out of the vector (leaving behind a
    // hole), shift along the others and move the removed element back into the
    // vector at the final location of the hole.
    // The `Hole` type is used to represent this, and make sure
    // the hole is filled back at the end of its scope, even on panic.
    // Using a hole reduces the constant factor compared to using swaps,
    // which involves twice as many moves.

    /// # Safety
    ///
    /// The caller must guarantee that `pos < self.len()`.
    ///
    /// Returns the new position of the element.
    #[requires(pos < self.len())]
    #[ensures(|result| *result <= pos)]
    #[cfg_attr(kani, kani::modifies(self.kani_slice()))]
    unsafe fn sift_up(&mut self, start: usize, pos: usize) -> usize {
        // Take out the value at `pos` and create a hole.
        // SAFETY: The caller guarantees that pos < self.len()
        let mut hole = unsafe { Hole::new(&mut self.data, pos) };

        // The hole only moves towards the root, so it stays inside the slice. A comparison
        // may write to its operands (interior mutability), so `hole.elt` is in the clause.
        #[cfg_attr(kani, kani::loop_invariant(hole.pos <= pos))]
        #[cfg_attr(kani, kani::loop_modifies(&hole.pos, &hole.elt, hole.kani_slice()))]
        #[cfg_attr(kani, kani::loop_decreases(hole.pos))]
        while hole.pos() > start {
            let parent = (hole.pos() - 1) / 2;

            // SAFETY: hole.pos() > start >= 0, which means hole.pos() > 0
            //  and so hole.pos() - 1 can't underflow.
            //  This guarantees that parent < hole.pos() so
            //  it's a valid index and also != hole.pos().
            if hole.element() <= unsafe { hole.get(parent) } {
                break;
            }

            // SAFETY: Same as above
            unsafe { hole.move_to(parent) };
        }

        hole.pos()
    }

    /// Take an element at `pos` and move it down the heap,
    /// while its children are larger.
    ///
    /// Returns the new position of the element.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that `pos < end <= self.len()`.
    #[requires(pos < end && end <= self.len())]
    #[ensures(|result| pos <= *result && *result < end)]
    #[cfg_attr(kani, kani::modifies(self.kani_slice()))]
    unsafe fn sift_down_range(&mut self, pos: usize, end: usize) -> usize {
        // SAFETY: The caller guarantees that pos < end <= self.len().
        let mut hole = unsafe { Hole::new(&mut self.data, pos) };
        let mut child = 2 * hole.pos() + 1;

        // Loop invariant: child == 2 * hole.pos() + 1.
        // `child` is the left child of the hole (so neither child is the hole itself), and
        // the hole stays inside `[pos, end)`.
        #[cfg_attr(kani, kani::loop_invariant(
            child % 2 == 1 && child / 2 == hole.pos && pos <= hole.pos && hole.pos < end
        ))]
        #[cfg_attr(kani, kani::loop_modifies(&hole.pos, &hole.elt, &child, hole.kani_slice()))]
        while child <= end.saturating_sub(2) {
            // compare with the greater of the two children
            // SAFETY: child < end - 1 < self.len() and
            //  child + 1 < end <= self.len(), so they're valid indexes.
            //  child == 2 * hole.pos() + 1 != hole.pos() and
            //  child + 1 == 2 * hole.pos() + 2 != hole.pos().
            // FIXME: 2 * hole.pos() + 1 or 2 * hole.pos() + 2 could overflow
            //  if T is a ZST
            child += unsafe { hole.get(child) <= hole.get(child + 1) } as usize;

            // if we are already in order, stop.
            // SAFETY: child is now either the old child or the old child+1
            //  We already proven that both are < self.len() and != hole.pos()
            if hole.element() >= unsafe { hole.get(child) } {
                return hole.pos();
            }

            // SAFETY: same as above.
            unsafe { hole.move_to(child) };
            child = 2 * hole.pos() + 1;
        }

        // SAFETY: && short circuit, which means that in the
        //  second condition it's already true that child == end - 1 < self.len().
        if child == end - 1 && hole.element() < unsafe { hole.get(child) } {
            // SAFETY: child is already proven to be a valid index and
            //  child == 2 * hole.pos() + 1 != hole.pos().
            unsafe { hole.move_to(child) };
        }

        hole.pos()
    }

    /// # Safety
    ///
    /// The caller must guarantee that `pos < self.len()`.
    #[requires(pos < self.len())]
    #[ensures(|result| pos <= *result && *result < self.len())]
    #[cfg_attr(kani, kani::modifies(self.kani_slice()))]
    unsafe fn sift_down(&mut self, pos: usize) -> usize {
        let len = self.len();
        // SAFETY: pos < len is guaranteed by the caller and
        //  obviously len = self.len() <= self.len().
        unsafe { self.sift_down_range(pos, len) }
    }

    /// Take an element at `pos` and move it all the way down the heap,
    /// then sift it up to its position.
    ///
    /// Note: This is faster when the element is known to be large / should
    /// be closer to the bottom.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that `pos < self.len()`.
    #[requires(pos < self.len())]
    #[cfg_attr(kani, kani::modifies(self.kani_slice()))]
    unsafe fn sift_down_to_bottom(&mut self, mut pos: usize) {
        let end = self.len();
        let start = pos;

        // SAFETY: The caller guarantees that pos < self.len().
        let mut hole = unsafe { Hole::new(&mut self.data, pos) };
        let mut child = 2 * hole.pos() + 1;

        // Loop invariant: child == 2 * hole.pos() + 1.
        // `child` is the left child of the hole (so neither child is the hole itself), and
        // the hole stays inside `[start, end)`.
        #[cfg_attr(kani, kani::loop_invariant(
            child % 2 == 1 && child / 2 == hole.pos && start <= hole.pos && hole.pos < end
        ))]
        #[cfg_attr(kani, kani::loop_modifies(&hole.pos, &hole.elt, &child, hole.kani_slice()))]
        while child <= end.saturating_sub(2) {
            // SAFETY: child < end - 1 < self.len() and
            //  child + 1 < end <= self.len(), so they're valid indexes.
            //  child == 2 * hole.pos() + 1 != hole.pos() and
            //  child + 1 == 2 * hole.pos() + 2 != hole.pos().
            // FIXME: 2 * hole.pos() + 1 or 2 * hole.pos() + 2 could overflow
            //  if T is a ZST
            child += unsafe { hole.get(child) <= hole.get(child + 1) } as usize;

            // SAFETY: Same as above
            unsafe { hole.move_to(child) };
            child = 2 * hole.pos() + 1;
        }

        if child == end - 1 {
            // SAFETY: child == end - 1 < self.len(), so it's a valid index
            //  and child == 2 * hole.pos() + 1 != hole.pos().
            unsafe { hole.move_to(child) };
        }
        pos = hole.pos();
        drop(hole);

        // SAFETY: pos is the position in the hole and was already proven
        //  to be a valid index.
        unsafe { self.sift_up(start, pos) };
    }

    /// Rebuild assuming data[0..start] is still a proper heap.
    fn rebuild_tail(&mut self, start: usize) {
        if start == self.len() {
            return;
        }

        let tail_len = self.len() - start;

        #[inline(always)]
        fn log2_fast(x: usize) -> usize {
            (usize::BITS - x.leading_zeros() - 1) as usize
        }

        // `rebuild` takes O(self.len()) operations
        // and about 2 * self.len() comparisons in the worst case
        // while repeating `sift_up` takes O(tail_len * log(start)) operations
        // and about 1 * tail_len * log_2(start) comparisons in the worst case,
        // assuming start >= tail_len. For larger heaps, the crossover point
        // no longer follows this reasoning and was determined empirically.
        let better_to_rebuild = if start < tail_len {
            true
        } else if self.len() <= 2048 {
            2 * self.len() < tail_len * log2_fast(start)
        } else {
            2 * self.len() < tail_len * 11
        };

        if better_to_rebuild {
            self.rebuild();
        } else {
            #[cfg_attr(kani, kani::loop_invariant(kani::index <= tail_len))]
            #[cfg_attr(kani, kani::loop_modifies(self.kani_slice()))]
            for i in start..self.len() {
                // SAFETY: The index `i` is always less than self.len().
                unsafe { self.sift_up(0, i) };
            }
        }
    }

    fn rebuild(&mut self) {
        let mut n = self.len() / 2;
        #[cfg_attr(kani, kani::loop_invariant(n <= self.data.len() / 2))]
        #[cfg_attr(kani, kani::loop_modifies(&n, self.kani_slice()))]
        #[cfg_attr(kani, kani::loop_decreases(n))]
        while n > 0 {
            n -= 1;
            // SAFETY: n starts from self.len() / 2 and goes down to 0.
            //  The only case when !(n < self.len()) is if
            //  self.len() == 0, but it's ruled out by the loop condition.
            unsafe { self.sift_down(n) };
        }
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    ///
    /// let mut a = BinaryHeap::from([-10, 1, 2, 3, 3]);
    /// let mut b = BinaryHeap::from([-20, 5, 43]);
    ///
    /// a.append(&mut b);
    ///
    /// assert_eq!(a.into_sorted_vec(), [-20, -10, 1, 2, 3, 3, 5, 43]);
    /// assert!(b.is_empty());
    /// ```
    #[stable(feature = "binary_heap_append", since = "1.11.0")]
    pub fn append(&mut self, other: &mut Self) {
        if self.len() < other.len() {
            swap(self, other);
        }

        let start = self.data.len();

        self.data.append(&mut other.data);

        self.rebuild_tail(start);
    }

    /// Clears the binary heap, returning an iterator over the removed elements
    /// in heap order. If the iterator is dropped before being fully consumed,
    /// it drops the remaining elements in heap order.
    ///
    /// The returned iterator keeps a mutable borrow on the heap to optimize
    /// its implementation.
    ///
    /// Note:
    /// * `.drain_sorted()` is *O*(*n* \* log(*n*)); much slower than `.drain()`.
    ///   You should use the latter for most cases.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(binary_heap_drain_sorted)]
    /// use std::collections::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::from([1, 2, 3, 4, 5]);
    /// assert_eq!(heap.len(), 5);
    ///
    /// drop(heap.drain_sorted()); // removes all elements in heap order
    /// assert_eq!(heap.len(), 0);
    /// ```
    #[inline]
    #[unstable(feature = "binary_heap_drain_sorted", issue = "59278")]
    pub fn drain_sorted(&mut self) -> DrainSorted<'_, T, A> {
        DrainSorted { inner: self }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns
    /// `false`. The elements are visited in unsorted (and unspecified) order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::from([-10, -5, 1, 2, 4, 13]);
    ///
    /// heap.retain(|x| x % 2 == 0); // only keep even numbers
    ///
    /// assert_eq!(heap.into_sorted_vec(), [-10, 2, 4])
    /// ```
    #[stable(feature = "binary_heap_retain", since = "1.70.0")]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        // rebuild_start will be updated to the first touched element below, and the rebuild will
        // only be done for the tail.
        let mut guard = RebuildOnDrop { rebuild_from: self.len(), heap: self };
        let mut i = 0;

        guard.heap.data.retain(|e| {
            let keep = f(e);
            if !keep && i < guard.rebuild_from {
                guard.rebuild_from = i;
            }
            i += 1;
            keep
        });
    }
}

impl<T, A: Allocator> BinaryHeap<T, A> {
    /// Returns an iterator visiting all values in the underlying vector, in
    /// arbitrary order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let heap = BinaryHeap::from([1, 2, 3, 4]);
    ///
    /// // Print 1, 2, 3, 4 in arbitrary order
    /// for x in heap.iter() {
    ///     println!("{x}");
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[cfg_attr(not(test), rustc_diagnostic_item = "binaryheap_iter")]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter { iter: self.data.iter() }
    }

    /// Returns an iterator which retrieves elements in heap order.
    ///
    /// This method consumes the original heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(binary_heap_into_iter_sorted)]
    /// use std::collections::BinaryHeap;
    /// let heap = BinaryHeap::from([1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(heap.into_iter_sorted().take(2).collect::<Vec<_>>(), [5, 4]);
    /// ```
    #[unstable(feature = "binary_heap_into_iter_sorted", issue = "59278")]
    pub fn into_iter_sorted(self) -> IntoIterSorted<T, A> {
        IntoIterSorted { inner: self }
    }

    /// Returns the greatest item in the binary heap, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::new();
    /// assert_eq!(heap.peek(), None);
    ///
    /// heap.push(1);
    /// heap.push(5);
    /// heap.push(2);
    /// assert_eq!(heap.peek(), Some(&5));
    ///
    /// ```
    ///
    /// # Time complexity
    ///
    /// Cost is *O*(1) in the worst case.
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn peek(&self) -> Option<&T> {
        self.data.get(0)
    }

    /// Returns the number of elements the binary heap can hold without reallocating.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::with_capacity(100);
    /// assert!(heap.capacity() >= 100);
    /// heap.push(4);
    /// ```
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    /// Reserves the minimum capacity for at least `additional` elements more than
    /// the current length. Unlike [`reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `reserve_exact`, capacity will be greater than or equal to
    /// `self.len() + additional`. Does nothing if the capacity is already
    /// sufficient.
    ///
    /// [`reserve`]: BinaryHeap::reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`usize`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::new();
    /// heap.reserve_exact(100);
    /// assert!(heap.capacity() >= 100);
    /// heap.push(4);
    /// ```
    ///
    /// [`reserve`]: BinaryHeap::reserve
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.data.reserve_exact(additional);
    }

    /// Reserves capacity for at least `additional` elements more than the
    /// current length. The allocator may reserve more space to speculatively
    /// avoid frequent allocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`usize`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::new();
    /// heap.reserve(100);
    /// assert!(heap.capacity() >= 100);
    /// heap.push(4);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn reserve(&mut self, additional: usize) {
        self.data.reserve(additional);
    }

    /// Tries to reserve the minimum capacity for at least `additional` elements
    /// more than the current length. Unlike [`try_reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `try_reserve_exact`, capacity will be greater than or
    /// equal to `self.len() + additional` if it returns `Ok(())`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`try_reserve`] if future insertions are expected.
    ///
    /// [`try_reserve`]: BinaryHeap::try_reserve
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// use std::collections::TryReserveError;
    ///
    /// fn find_max_slow(data: &[u32]) -> Result<Option<u32>, TryReserveError> {
    ///     let mut heap = BinaryHeap::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     heap.try_reserve_exact(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     heap.extend(data.iter());
    ///
    ///     Ok(heap.pop())
    /// }
    /// # find_max_slow(&[1, 2, 3]).expect("reserving capacity for 12 bytes should never fail");
    /// ```
    #[stable(feature = "try_reserve_2", since = "1.63.0")]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.data.try_reserve_exact(additional)
    }

    /// Tries to reserve capacity for at least `additional` elements more than the
    /// current length. The allocator may reserve more space to speculatively
    /// avoid frequent allocations. After calling `try_reserve`, capacity will be
    /// greater than or equal to `self.len() + additional` if it returns
    /// `Ok(())`. Does nothing if capacity is already sufficient. This method
    /// preserves the contents even if an error occurs.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// use std::collections::TryReserveError;
    ///
    /// fn find_max_slow(data: &[u32]) -> Result<Option<u32>, TryReserveError> {
    ///     let mut heap = BinaryHeap::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     heap.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     heap.extend(data.iter());
    ///
    ///     Ok(heap.pop())
    /// }
    /// # find_max_slow(&[1, 2, 3]).expect("reserving capacity for 12 bytes should never fail");
    /// ```
    #[stable(feature = "try_reserve_2", since = "1.63.0")]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.data.try_reserve(additional)
    }

    /// Discards as much additional capacity as possible.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap: BinaryHeap<i32> = BinaryHeap::with_capacity(100);
    ///
    /// assert!(heap.capacity() >= 100);
    /// heap.shrink_to_fit();
    /// assert!(heap.capacity() == 0);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn shrink_to_fit(&mut self) {
        self.data.shrink_to_fit();
    }

    /// Discards capacity with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap: BinaryHeap<i32> = BinaryHeap::with_capacity(100);
    ///
    /// assert!(heap.capacity() >= 100);
    /// heap.shrink_to(10);
    /// assert!(heap.capacity() >= 10);
    /// ```
    #[inline]
    #[stable(feature = "shrink_to", since = "1.56.0")]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.data.shrink_to(min_capacity)
    }

    /// Returns a slice of all values in the underlying vector, in arbitrary
    /// order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// use std::io::{self, Write};
    ///
    /// let heap = BinaryHeap::from([1, 2, 3, 4, 5, 6, 7]);
    ///
    /// io::sink().write(heap.as_slice()).unwrap();
    /// ```
    #[must_use]
    #[stable(feature = "binary_heap_as_slice", since = "1.80.0")]
    pub fn as_slice(&self) -> &[T] {
        self.data.as_slice()
    }

    /// Returns a mutable slice of all values in the underlying vector.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the slice remains a max-heap, i.e. for all indices
    /// `0 < i < slice.len()`, `slice[(i - 1) / 2] >= slice[i]`, before the borrow ends
    /// and the binary heap is used.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(binary_heap_as_mut_slice)]
    ///
    /// use std::collections::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::<u32>::from([1, 2, 3, 4, 5, 6, 7]);
    ///
    /// unsafe {
    ///     for value in heap.as_mut_slice() {
    ///         *value = (*value).saturating_mul(2);
    ///     }
    /// }
    /// ```
    #[must_use]
    #[unstable(feature = "binary_heap_as_mut_slice", issue = "154009")]
    pub unsafe fn as_mut_slice(&mut self) -> &mut [T] {
        self.data.as_mut_slice()
    }

    /// Consumes the `BinaryHeap` and returns the underlying vector
    /// in arbitrary order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let heap = BinaryHeap::from([1, 2, 3, 4, 5, 6, 7]);
    /// let vec = heap.into_vec();
    ///
    /// // Will print in some order
    /// for x in vec {
    ///     println!("{x}");
    /// }
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "binary_heap_extras_15", since = "1.5.0")]
    pub fn into_vec(self) -> Vec<T, A> {
        self.into()
    }

    /// Returns a reference to the underlying allocator.
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")]
    #[inline]
    pub fn allocator(&self) -> &A {
        self.data.allocator()
    }

    /// Returns the length of the binary heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let heap = BinaryHeap::from([1, 3]);
    ///
    /// assert_eq!(heap.len(), 2);
    /// ```
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("length", "size")]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Checks if the binary heap is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::new();
    ///
    /// assert!(heap.is_empty());
    ///
    /// heap.push(3);
    /// heap.push(5);
    /// heap.push(1);
    ///
    /// assert!(!heap.is_empty());
    /// ```
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the binary heap, returning an iterator over the removed elements
    /// in arbitrary order. If the iterator is dropped before being fully
    /// consumed, it drops the remaining elements in arbitrary order.
    ///
    /// The returned iterator keeps a mutable borrow on the heap to optimize
    /// its implementation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::from([1, 3]);
    ///
    /// assert!(!heap.is_empty());
    ///
    /// for x in heap.drain() {
    ///     println!("{x}");
    /// }
    ///
    /// assert!(heap.is_empty());
    /// ```
    #[inline]
    #[stable(feature = "drain", since = "1.6.0")]
    pub fn drain(&mut self) -> Drain<'_, T, A>
    where
        A: AllocatorNightly, // needed for the `Vec::drain` call
    {
        Drain { iter: self.data.drain(..) }
    }

    /// Drops all items from the binary heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::from([1, 3]);
    ///
    /// assert!(!heap.is_empty());
    ///
    /// heap.clear();
    ///
    /// assert!(heap.is_empty());
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn clear(&mut self)
    where
        A: AllocatorNightly,
    {
        self.drain();
    }
}

/// The elements of the heap, as the memory that the loop and function contracts of the sift
/// functions allow them to write to.
#[cfg(kani)]
impl<T, A: Allocator> BinaryHeap<T, A> {
    fn kani_slice(&self) -> *const [T] {
        ptr::slice_from_raw_parts(self.data.as_ptr(), self.data.len())
    }
}

/// The slice that a hole is in, as the memory that the loop contracts allow `move_to` to
/// write to.
#[cfg(kani)]
impl<T> Hole<'_, T> {
    fn kani_slice(&self) -> *const [T] {
        ptr::slice_from_raw_parts(self.data.as_ptr(), self.data.len())
    }
}

/// Hole represents a hole in a slice i.e., an index without valid value
/// (because it was moved from or duplicated).
/// In drop, `Hole` will restore the slice by filling the hole
/// position with the value that was originally removed.
struct Hole<'a, T: 'a> {
    data: &'a mut [T],
    elt: ManuallyDrop<T>,
    pos: usize,
}

impl<'a, T> Hole<'a, T> {
    /// Creates a new `Hole` at index `pos`.
    ///
    /// # Safety
    ///
    /// `pos` must be within the data slice.
    #[inline]
    #[requires(pos < data.len())]
    #[ensures(|hole| hole.pos == pos && hole.data.len() == old(data.len()))]
    unsafe fn new(data: &'a mut [T], pos: usize) -> Self {
        debug_assert!(pos < data.len());
        // SAFETY: Caller ensures pos is inside the slice.
        let elt = unsafe { ptr::read(data.get_unchecked(pos)) };
        Hole { data, elt: ManuallyDrop::new(elt), pos }
    }

    #[inline]
    fn pos(&self) -> usize {
        self.pos
    }

    /// Returns a reference to the element removed.
    #[inline]
    fn element(&self) -> &T {
        &self.elt
    }

    /// Returns a reference to the element at `index`.
    ///
    /// # Safety
    ///
    /// `index` must be within the data slice and not equal to the current position.
    #[inline]
    #[requires(index != self.pos && index < self.data.len())]
    #[ensures(|result| ptr::eq(*result, self.data.as_ptr().wrapping_add(index)))]
    unsafe fn get(&self, index: usize) -> &T {
        debug_assert!(index != self.pos);
        debug_assert!(index < self.data.len());
        // SAFETY: Upheld by caller.
        unsafe { self.data.get_unchecked(index) }
    }

    /// Move hole to new location
    ///
    /// # Safety
    ///
    /// `index` must be within the data slice and not equal to the current position.
    #[inline]
    // `self.pos < self.data.len()` is the invariant of `Hole`: `new` establishes it and
    // `move_to` keeps it.
    #[requires(self.pos < self.data.len())]
    #[requires(index != self.pos && index < self.data.len())]
    #[ensures(|_| self.pos == index)]
    #[cfg_attr(kani, kani::modifies(&self.pos, self.data.as_ptr().wrapping_add(self.pos)))]
    unsafe fn move_to(&mut self, index: usize) {
        debug_assert!(index != self.pos);
        debug_assert!(index < self.data.len());
        let ptr = self.data.as_mut_ptr();
        // ignore-tidy-undocumented-unsafe
        unsafe {
            let index_ptr: *const _ = ptr.add(index);
            let hole_ptr = ptr.add(self.pos);
            ptr::copy_nonoverlapping(index_ptr, hole_ptr, 1);
        }
        self.pos = index;
    }
}

impl<T> Drop for Hole<'_, T> {
    #[inline]
    fn drop(&mut self) {
        // fill the hole again
        let pos = self.pos;
        // ignore-tidy-undocumented-unsafe
        unsafe {
            ptr::copy_nonoverlapping(&*self.elt, self.data.get_unchecked_mut(pos), 1);
        }
    }
}

/// An iterator over the elements of a `BinaryHeap`.
///
/// This `struct` is created by [`BinaryHeap::iter()`]. See its
/// documentation for more.
///
/// [`iter`]: BinaryHeap::iter
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct Iter<'a, T: 'a> {
    iter: slice::Iter<'a, T>,
}

#[stable(feature = "default_iters_sequel", since = "1.82.0")]
impl<T> Default for Iter<'_, T> {
    /// Creates an empty `binary_heap::Iter`.
    ///
    /// ```
    /// # use std::collections::binary_heap;
    /// let iter: binary_heap::Iter<'_, u8> = Default::default();
    /// assert_eq!(iter.len(), 0);
    /// ```
    fn default() -> Self {
        Iter { iter: Default::default() }
    }
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Iter").field(&self.iter.as_slice()).finish()
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
#[stable(feature = "rust1", since = "1.0.0")]
impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter { iter: self.iter.clone() }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(self) -> Option<&'a T> {
        self.iter.last()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a T> {
        self.iter.next_back()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> ExactSizeIterator for Iter<'_, T> {
    fn is_empty(&self) -> bool {
        self.iter.is_empty()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<T> FusedIterator for Iter<'_, T> {}

/// An owning iterator over the elements of a `BinaryHeap`.
///
/// This `struct` is created by [`BinaryHeap::into_iter()`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: BinaryHeap::into_iter
#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Clone)]
pub struct IntoIter<
    T,
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")] A: Allocator = Global,
> {
    iter: vec::IntoIter<T, A>,
}

impl<T, A: Allocator> IntoIter<T, A> {
    /// Returns a reference to the underlying allocator.
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")]
    pub fn allocator(&self) -> &A {
        self.iter.allocator()
    }
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl<T: fmt::Debug, A: Allocator> fmt::Debug for IntoIter<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoIter").field(&self.iter.as_slice()).finish()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> Iterator for IntoIter<T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> DoubleEndedIterator for IntoIter<T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> ExactSizeIterator for IntoIter<T, A> {
    fn is_empty(&self) -> bool {
        self.iter.is_empty()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<T, A: Allocator> FusedIterator for IntoIter<T, A> {}

#[doc(hidden)]
#[unstable(issue = "none", feature = "trusted_fused")]
unsafe impl<T, A: Allocator> TrustedFused for IntoIter<T, A> {}

#[stable(feature = "default_iters", since = "1.70.0")]
impl<T> Default for IntoIter<T> {
    /// Creates an empty `binary_heap::IntoIter`.
    ///
    /// ```
    /// # use std::collections::binary_heap;
    /// let iter: binary_heap::IntoIter<u8> = Default::default();
    /// assert_eq!(iter.len(), 0);
    /// ```
    fn default() -> Self {
        IntoIter { iter: Default::default() }
    }
}

// In addition to the SAFETY invariants of the following three unsafe traits
// also refer to the vec::in_place_collect module documentation to get an overview
#[unstable(issue = "none", feature = "inplace_iteration")]
#[doc(hidden)]
unsafe impl<T, A: Allocator> SourceIter for IntoIter<T, A> {
    type Source = IntoIter<T, A>;

    #[inline]
    unsafe fn as_inner(&mut self) -> &mut Self::Source {
        self
    }
}

#[unstable(issue = "none", feature = "inplace_iteration")]
#[doc(hidden)]
unsafe impl<I, A: Allocator> InPlaceIterable for IntoIter<I, A> {
    const EXPAND_BY: Option<NonZero<usize>> = NonZero::new(1);
    const MERGE_BY: Option<NonZero<usize>> = NonZero::new(1);
}

#[cfg(not(test))]
unsafe impl<I> AsVecIntoIter for IntoIter<I> {
    type Item = I;

    fn as_into_iter(&mut self) -> &mut vec::IntoIter<Self::Item> {
        &mut self.iter
    }
}

#[must_use = "iterators are lazy and do nothing unless consumed"]
#[unstable(feature = "binary_heap_into_iter_sorted", issue = "59278")]
#[derive(Clone, Debug)]
pub struct IntoIterSorted<
    T,
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")] A: Allocator = Global,
> {
    inner: BinaryHeap<T, A>,
}

impl<T, A: Allocator> IntoIterSorted<T, A> {
    /// Returns a reference to the underlying allocator.
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")]
    pub fn allocator(&self) -> &A {
        self.inner.allocator()
    }
}

#[unstable(feature = "binary_heap_into_iter_sorted", issue = "59278")]
impl<T: Ord, A: Allocator> Iterator for IntoIterSorted<T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.inner.pop()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.inner.len();
        (exact, Some(exact))
    }
}

#[unstable(feature = "binary_heap_into_iter_sorted", issue = "59278")]
impl<T: Ord, A: Allocator> ExactSizeIterator for IntoIterSorted<T, A> {}

#[unstable(feature = "binary_heap_into_iter_sorted", issue = "59278")]
impl<T: Ord, A: Allocator> FusedIterator for IntoIterSorted<T, A> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T: Ord, A: Allocator> TrustedLen for IntoIterSorted<T, A> {}

/// A draining iterator over the elements of a `BinaryHeap`.
///
/// This `struct` is created by [`BinaryHeap::drain()`]. See its
/// documentation for more.
///
/// [`drain`]: BinaryHeap::drain
#[stable(feature = "drain", since = "1.6.0")]
#[derive(Debug)]
pub struct Drain<
    'a,
    T: 'a,
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")] A: Allocator = Global,
> {
    iter: vec::Drain<'a, T, A>,
}

impl<T, A: Allocator> Drain<'_, T, A> {
    /// Returns a reference to the underlying allocator.
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")]
    pub fn allocator(&self) -> &A {
        self.iter.allocator()
    }
}

#[stable(feature = "drain", since = "1.6.0")]
impl<T, A: Allocator> Iterator for Drain<'_, T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[stable(feature = "drain", since = "1.6.0")]
impl<T, A: Allocator> DoubleEndedIterator for Drain<'_, T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back()
    }
}

#[stable(feature = "drain", since = "1.6.0")]
impl<T, A: Allocator> ExactSizeIterator for Drain<'_, T, A> {
    fn is_empty(&self) -> bool {
        self.iter.is_empty()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<T, A: Allocator> FusedIterator for Drain<'_, T, A> {}

/// A draining iterator over the elements of a `BinaryHeap`.
///
/// This `struct` is created by [`BinaryHeap::drain_sorted()`]. See its
/// documentation for more.
///
/// [`drain_sorted`]: BinaryHeap::drain_sorted
#[unstable(feature = "binary_heap_drain_sorted", issue = "59278")]
#[derive(Debug)]
pub struct DrainSorted<
    'a,
    T: Ord,
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")] A: Allocator = Global,
> {
    inner: &'a mut BinaryHeap<T, A>,
}

impl<'a, T: Ord, A: Allocator> DrainSorted<'a, T, A> {
    /// Returns a reference to the underlying allocator.
    #[unstable(feature = "allocator_ext", issue = "163177", implied_by = "allocator_api")]
    pub fn allocator(&self) -> &A {
        self.inner.allocator()
    }
}

#[unstable(feature = "binary_heap_drain_sorted", issue = "59278")]
impl<'a, T: Ord, A: Allocator> Drop for DrainSorted<'a, T, A> {
    /// Removes heap elements in heap order.
    fn drop(&mut self) {
        struct DropGuard<'r, 'a, T: Ord, A: Allocator>(&'r mut DrainSorted<'a, T, A>);

        impl<'r, 'a, T: Ord, A: Allocator> Drop for DropGuard<'r, 'a, T, A> {
            fn drop(&mut self) {
                while self.0.inner.pop().is_some() {}
            }
        }

        while let Some(item) = self.inner.pop() {
            let guard = DropGuard(self);
            drop(item);
            mem::forget(guard);
        }
    }
}

#[unstable(feature = "binary_heap_drain_sorted", issue = "59278")]
impl<T: Ord, A: Allocator> Iterator for DrainSorted<'_, T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.inner.pop()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.inner.len();
        (exact, Some(exact))
    }
}

#[unstable(feature = "binary_heap_drain_sorted", issue = "59278")]
impl<T: Ord, A: Allocator> ExactSizeIterator for DrainSorted<'_, T, A> {}

#[unstable(feature = "binary_heap_drain_sorted", issue = "59278")]
impl<T: Ord, A: Allocator> FusedIterator for DrainSorted<'_, T, A> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T: Ord, A: Allocator> TrustedLen for DrainSorted<'_, T, A> {}

#[stable(feature = "binary_heap_extras_15", since = "1.5.0")]
impl<T: Ord, A: AllocatorNightly> From<Vec<T, A>> for BinaryHeap<T, A> {
    /// Converts a `Vec<T>` into a `BinaryHeap<T>`.
    ///
    /// This conversion happens in-place, and has *O*(*n*) time complexity.
    fn from(vec: Vec<T, A>) -> BinaryHeap<T, A> {
        let mut heap = BinaryHeap { data: vec };
        heap.rebuild();
        heap
    }
}

#[stable(feature = "std_collections_from_array", since = "1.56.0")]
impl<T: Ord, const N: usize> From<[T; N]> for BinaryHeap<T> {
    /// ```
    /// use std::collections::BinaryHeap;
    ///
    /// let mut h1 = BinaryHeap::from([1, 4, 2, 3]);
    /// let mut h2: BinaryHeap<_> = [1, 4, 2, 3].into();
    /// while let Some((a, b)) = h1.pop().zip(h2.pop()) {
    ///     assert_eq!(a, b);
    /// }
    /// ```
    fn from(arr: [T; N]) -> Self {
        Self::from_iter(arr)
    }
}

#[stable(feature = "binary_heap_extras_15", since = "1.5.0")]
impl<T, A: Allocator> From<BinaryHeap<T, A>> for Vec<T, A> {
    /// Converts a `BinaryHeap<T>` into a `Vec<T>`.
    ///
    /// This conversion requires no data movement or allocation, and has
    /// constant time complexity.
    fn from(heap: BinaryHeap<T, A>) -> Vec<T, A> {
        heap.data
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Ord> FromIterator<T> for BinaryHeap<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> BinaryHeap<T> {
        BinaryHeap::from(iter.into_iter().collect::<Vec<_>>())
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> IntoIterator for BinaryHeap<T, A> {
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    /// Creates a consuming iterator, that is, one that moves each value out of
    /// the binary heap in arbitrary order. The binary heap cannot be used
    /// after calling this.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BinaryHeap;
    /// let heap = BinaryHeap::from([1, 2, 3, 4]);
    ///
    /// // Print 1, 2, 3, 4 in arbitrary order
    /// for x in heap.into_iter() {
    ///     // x has type i32, not &i32
    ///     println!("{x}");
    /// }
    /// ```
    fn into_iter(self) -> IntoIter<T, A> {
        IntoIter { iter: self.data.into_iter() }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T, A: Allocator> IntoIterator for &'a BinaryHeap<T, A> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Ord, A: Allocator> Extend<T> for BinaryHeap<T, A> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let guard = RebuildOnDrop { rebuild_from: self.len(), heap: self };
        guard.heap.data.extend(iter);
    }

    #[inline]
    fn extend_one(&mut self, item: T) {
        self.push(item);
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}

#[stable(feature = "extend_ref", since = "1.2.0")]
impl<'a, T: 'a + Ord + Copy, A: Allocator> Extend<&'a T> for BinaryHeap<T, A> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }

    #[inline]
    fn extend_one(&mut self, &item: &'a T) {
        self.push(item);
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    //! Challenge 31: safety of `BinaryHeap`.
    //!
    //! Every harness calls the shipped function on a heap of symbolic capacity and length.
    //! Every comparison returns an arbitrary result, so no harness relies on the elements being
    //! ordered as a max-heap. No harness has an unwinding bound: the loops of `sift_up`,
    //! `sift_down_range`, `sift_down_to_bottom`, `rebuild`, `rebuild_tail` and
    //! `into_sorted_vec` have loop contracts. No function is stubbed.
    //!
    //! # Element types (generic `T`)
    //!
    //! Kani verifies instantiations, not generic functions. Each proof is written once, as a
    //! function `check_*::<T>`, and instantiated for the element types listed at the end of this
    //! module. This is option A of issue #734. The rest of this section is the argument that the
    //! instantiations cover every `T`.
    //!
    //! ## What the functions observe of `T`
    //!
    //! * Its layout, but only through the functions they call. `binary_heap/mod.rs` never asks
    //!   for the size or the alignment of `T`: it addresses elements by index and moves them
    //!   whole, with `ptr::read`, `ptr::copy_nonoverlapping`, `ptr::swap`, `mem::swap` and
    //!   methods of `Vec`.
    //! * Its invalid bit patterns, if it has some: `pop` returns an `Option<T>`, which stores
    //!   `None` in one of them.
    //! * The comparison operators of `PartialOrd` (`<`, `<=`, `>=`), the only trait methods of
    //!   `T` that are called.
    //!
    //! They never drop, clone or create an element, and they read the bytes of an element
    //! only through that `Option`.
    //!
    //! ## How each is covered
    //!
    //! * Comparisons. In every element type, each comparison returns an arbitrary result
    //!   (`AnyOrd`), independent of the operands and of every other call. In `CellOrd` it also
    //!   overwrites both operands, as an `Ord` with interior mutability may. A comparison
    //!   receives two `&T`, never the slot of the hole (`index != pos` in the contracts of
    //!   `Hole`), and the heap is exclusively borrowed during the call, so safe code in `Ord`
    //!   cannot reach the heap in any other way. A comparison that panics is out of the scope of
    //!   the challenge.
    //! * Destructors. `DropFails` fails the proof when an element is dropped, so the functions
    //!   in scope run no destructor of `T`: they only move elements.
    //! * Invalid bit patterns. `bool`. The elements of a generated heap are all-zero, which is
    //!   a valid value of every element type here (`Element`).
    //! * Size and alignment: every branch on them in the functions called.
    //!   * Zero-sized or not, in `RawVecInner::{capacity, current_memory, grow_amortized}`,
    //!     `ptr::swap_nonoverlapping`, `Global::{alloc_impl_runtime, grow_impl_runtime}` and the
    //!     precondition checks of `slice::from_raw_parts_mut` and of the pointer functions: `()`,
    //!     and every other type. `grow_amortized` is only reached with a zero-sized type when
    //!     the vector is full (`panic_push_full`, `panic_append_too_long`).
    //!   * `raw_vec::min_non_zero_cap`, when `push` or `append` reallocates: size 1 (`u8`,
    //!     `bool`), up to 1 KiB (the types of 2 to 16 bytes), larger (`[u64; 256]`, 2 KiB). The
    //!     harnesses of `push` and `append` have a `kani::cover` for the reallocation.
    //!   * `ptr::swap_nonoverlapping_bytes`, from `mem::swap` in `pop`: whole words only (8, 16
    //!     and 2048 bytes); a tail only, of 1, 2, 4 and 4 + 2 bytes (`u8`, `u16`, `u32`,
    //!     `[u8; 6]`); a word and a tail (`Padded`, 12 bytes).
    //!   * Alignment: 1, 2, 4, 8 and 16. It is only compared between the old and the new layout
    //!     of a reallocation, which are equal.
    //!
    //!   One arm is not reached: `Layout::repeat_packed` fails, and `RawVec` panics with
    //!   "capacity overflow", when a buffer would exceed `isize::MAX` bytes, which is above
    //!   `MAX_BYTES`. The zero-sized case of that panic is reached (see above).
    //!
    //! ## Why another type cannot behave differently
    //!
    //! Two types that take the same arm of every branch above run the same instructions. They
    //! can still differ in three ways.
    //!
    //! * Byte offsets. An element is at `buffer + index * size_of::<T>()`. Each access proved
    //!   here has `index < len`, and a `Vec` guarantees `len <= capacity`, a buffer of
    //!   `capacity * size_of::<T>()` bytes that is at most `isize::MAX` bytes long, and a
    //!   buffer aligned for `T`. So the offset does not overflow and stays inside the buffer,
    //!   and the address is aligned because the size of a type is a multiple of its alignment.
    //!   None of this depends on the value of `size_of::<T>()`.
    //! * Lengths. The indices are computed from the length and from the results of the
    //!   comparisons only, so they are the same for every `T` at a given length. The harnesses
    //!   of the zero-sized type run for every length up to `usize::MAX`, and those of a sized
    //!   type for every buffer of up to `MAX_BYTES` bytes. A longer buffer of a sized type is
    //!   not checked by Kani: for it, the two items above are the argument.
    //! * Capacity arithmetic. The functions in scope do none. It happens in `Vec::push` and
    //!   `Vec::append` (`RawVecInner::grow_amortized`), which the challenge allows to assume
    //!   correct, and which `verifast-proofs/alloc/raw_vec` verifies for any element layout.
    //!   Here it runs for each element type, with a symbolic length and capacity.
    //!
    //! ## Not covered
    //!
    //! * Element types with padding other than `Padded`, and with invalid bit patterns other
    //!   than `bool`: the functions move whole elements and never produce one, so the bytes of
    //!   an element do not matter to them.
    //! * Unwinding out of a comparison (out of the scope of the challenge), and comparisons
    //!   with unsafe code of their own.
    //!
    //! # Lengths that only a zero-sized type has
    //!
    //! A heap of a zero-sized type can be longer than `isize::MAX`. Then `2 * pos + 1` can
    //! overflow in the sift-down loops (the FIXME in `sift_down_range`), and `2 * len` and
    //! `tail_len * 11` in the heuristic of `rebuild_tail`; a full vector cannot grow. The
    //! challenge accepts an overflow panic there. The harnesses of each element type take
    //! the inputs for which nothing overflows: for the three sift-down functions,
    //! `rebuild_tail`, `push` and `append` these are all such inputs, and the other
    //! functions, which reach the overflows only through those six, use heaps of at most
    //! `MAX_SIFT_DOWN_LEN` elements. The `panic_*` harnesses run inputs from the rest. They
    //! pass when an execution panics and no check other than a panic fails. They do not
    //! run every input of the rest. When the hole starts at or below `isize::MAX` in a
    //! longer heap, the comparisons decide whether an overflow is reached. And the inputs
    //! for which the heuristic of `rebuild_tail` overflows are not run: a harness for
    //! `2 * len` and one for `tail_len * 11` need about 10 GB of memory each.
    //!
    //! # Models and limits
    //!
    //! * The buffer of a heap is a real allocation that the allocator returns zeroed
    //!   (`Allocator::allocate_zeroed`), so every element is initialized, to the all-zero
    //!   value. The proofs do not depend on which valid values the elements have: the
    //!   functions only move elements (and wrap one in an `Option`), and a comparison
    //!   returns an arbitrary result whatever its operands are.
    //!   (Filling the buffer with an arbitrary byte instead, with `ptr::write_bytes`, makes
    //!   CBMC run out of memory when it reports the results of the `bool` harnesses built on
    //!   `pop`: Kani issue #4905.)
    //! * The buffer of a sized type is at most `MAX_BYTES` long, because of CBMC's object model
    //!   (see `MAX_BYTES`).
    //! * The loop contracts state where the hole is, not what the elements are. After a loop
    //!   with a contract, Kani therefore treats every element as arbitrary bytes, which for
    //!   `bool` includes invalid bit patterns. The functions in scope never read an element
    //!   after such a loop, except to compare it; a harness must not either
    //!   (`check_peek_mut_deref_mut_leak` pops before it pushes for this reason).
    //! * Kani runs the `for` loop of `rebuild_tail` as a `while` loop over its own model of the
    //!   range iterator (`kani::KaniIter`), as for every `for` loop with a loop contract.
    //! * A heap whose element type has a destructor is leaked at the end of a harness: dropping
    //!   a vector of symbolic length runs the drop glue of `[T]`, a loop of `Vec` without a
    //!   bound.
    //!
    //! # Not proved
    //!
    //! * That no element is duplicated or lost by a sift. Each step is checked (the contract of
    //!   `Hole::move_to` allows it to write the slot of the hole only, and no destructor runs),
    //!   but the loop contracts do not track the contents of the slice.
    //! * Termination of the loops of `sift_down_range`, `sift_down_to_bottom` and
    //!   `rebuild_tail`: the pinned Kani only accepts a variable as a termination measure. (The
    //!   other three loops have a `loop_decreases` clause.)
    //! * Panics in `Ord`, and `Drop for DrainSorted`, which are not in the scope of the
    //!   challenge.

    use core::alloc::Layout;
    use core::cell::Cell;
    use core::cmp::Ordering;
    use core::kani;

    use super::*;
    use crate::alloc::handle_alloc_error;

    /// The longest buffer of a heap in these harnesses, in bytes. `scripts/run-kani.sh` runs
    /// CBMC with `--object-bits 12`, which leaves 52 bits for the offset of a pointer inside
    /// its object; 2^48 bytes stay well inside them. It is a bound of these proofs: see
    /// "Why another type cannot behave differently" above for longer buffers.
    const MAX_BYTES: usize = 1 << 48;

    /// Largest length for which the child index `2 * pos + 1` of every `pos < len` fits in
    /// a `usize`. Only a heap of a zero-sized type can be longer.
    const MAX_SIFT_DOWN_LEN: usize = isize::MAX as usize + 1;

    // ------------------------------------------------------------------------------------
    // Element types

    fn any_ordering() -> Ordering {
        if kani::any() {
            Ordering::Less
        } else if kani::any() {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }

    /// An element with the layout of `V` whose comparisons return arbitrary results: each
    /// call is independent of the operands and of every other call. This covers every
    /// `Ord` implementation that returns, including inconsistent ones.
    struct AnyOrd<V>(V);

    impl<V> PartialEq for AnyOrd<V> {
        fn eq(&self, _: &Self) -> bool {
            kani::any()
        }
    }
    impl<V> Eq for AnyOrd<V> {}
    impl<V> PartialOrd for AnyOrd<V> {
        fn partial_cmp(&self, _: &Self) -> Option<Ordering> {
            if kani::any() { Some(any_ordering()) } else { None }
        }
        fn lt(&self, _: &Self) -> bool {
            kani::any()
        }
        fn le(&self, _: &Self) -> bool {
            kani::any()
        }
        fn gt(&self, _: &Self) -> bool {
            kani::any()
        }
        fn ge(&self, _: &Self) -> bool {
            kani::any()
        }
    }
    impl<V> Ord for AnyOrd<V> {
        fn cmp(&self, _: &Self) -> Ordering {
            any_ordering()
        }
    }
    impl<V: kani::Arbitrary> kani::Arbitrary for AnyOrd<V> {
        fn any() -> Self {
            AnyOrd(kani::any())
        }
    }

    /// An element whose comparisons also overwrite both operands, through a `Cell`: an
    /// `Ord` implementation is free to have such side effects.
    struct CellOrd(Cell<u64>);

    impl CellOrd {
        fn touch(&self, other: &Self) -> bool {
            self.0.set(kani::any());
            other.0.set(kani::any());
            kani::any()
        }
    }
    impl PartialEq for CellOrd {
        fn eq(&self, other: &Self) -> bool {
            self.touch(other)
        }
    }
    impl Eq for CellOrd {}
    impl PartialOrd for CellOrd {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            if self.touch(other) { Some(any_ordering()) } else { None }
        }
        fn lt(&self, other: &Self) -> bool {
            self.touch(other)
        }
        fn le(&self, other: &Self) -> bool {
            self.touch(other)
        }
        fn gt(&self, other: &Self) -> bool {
            self.touch(other)
        }
        fn ge(&self, other: &Self) -> bool {
            self.touch(other)
        }
    }
    impl Ord for CellOrd {
        fn cmp(&self, other: &Self) -> Ordering {
            self.touch(other);
            any_ordering()
        }
    }
    impl kani::Arbitrary for CellOrd {
        fn any() -> Self {
            CellOrd(Cell::new(kani::any()))
        }
    }

    /// A value that must not be dropped: its destructor fails the proof. As the element of
    /// a heap (`AnyOrd<DropFails>`) it shows that the functions in scope never drop an
    /// element: they only move elements, so none is dropped twice or after it has moved.
    struct DropFails(u16);

    impl Drop for DropFails {
        fn drop(&mut self) {
            panic!("an element was dropped");
        }
    }
    impl kani::Arbitrary for DropFails {
        fn any() -> Self {
            DropFails(kani::any())
        }
    }

    /// A value with padding: 12 bytes, 3 of them padding after `a`.
    #[repr(C)]
    struct Padded {
        a: u8,
        b: u32,
        c: u32,
    }

    impl kani::Arbitrary for Padded {
        fn any() -> Self {
            Padded { a: kani::any(), b: kani::any(), c: kani::any() }
        }
    }

    /// An element type of the harnesses. All-zero bytes must be a valid value of the type:
    /// the generator `any_vec` relies on it.
    trait Element: Ord + kani::Arbitrary {}

    macro_rules! all_zero_is_valid {
        ($($t:ty),* $(,)?) => { $(impl Element for $t {})* };
    }
    all_zero_is_valid!(
        AnyOrd<()>,
        AnyOrd<u8>,
        // `bool` has a validity invariant: only the bytes 0 (`false`) and 1 are values of it.
        AnyOrd<bool>,
        AnyOrd<DropFails>,
        AnyOrd<u32>,
        AnyOrd<u64>,
        AnyOrd<u128>,
        AnyOrd<[u64; 256]>,
        AnyOrd<[u8; 6]>,
        AnyOrd<Padded>,
        CellOrd,
    );

    // ------------------------------------------------------------------------------------
    // Generators

    /// Any vector: any capacity, any length, and every element initialized to a valid value.
    ///
    /// The buffer is a real allocation of the global allocator, which returns it zeroed, and
    /// all-zero bytes are a valid `T` (`Element`).
    fn any_vec<T: Element>() -> Vec<T> {
        if size_of::<T>() == 0 {
            let mut vec = Vec::new();
            // SAFETY: a vector of a zero-sized type has capacity `usize::MAX`, and its
            // elements have no bytes to initialize.
            unsafe { vec.set_len(kani::any()) };
            return vec;
        }
        let cap: usize = kani::any_where(|cap: &usize| *cap <= MAX_BYTES / size_of::<T>());
        let len: usize = kani::any_where(|len: &usize| *len <= cap);
        if cap == 0 {
            // A vector of capacity 0 has no allocation.
            return Vec::new();
        }
        let layout = Layout::array::<T>(cap).unwrap();
        let Ok(buffer) = Global.allocate_zeroed(layout) else { handle_alloc_error(layout) };
        // SAFETY: the buffer comes from the global allocator with the layout of `[T; cap]`,
        // `len <= cap`, and every byte of it is zero, so its elements are valid values.
        unsafe { Vec::from_raw_parts(buffer.as_ptr().cast::<T>(), len, cap) }
    }

    /// Any heap: any length, any capacity. Its elements are not ordered as a max-heap as far
    /// as the functions can tell: the comparisons return arbitrary results.
    fn any_heap<T: Element>() -> BinaryHeap<T> {
        BinaryHeap { data: any_vec() }
    }

    /// Any heap of at most `MAX_SIFT_DOWN_LEN` elements: no child index can overflow in it.
    /// A longer heap only exists for a zero-sized type (see "Lengths that only a zero-sized
    /// type has" at the top of this module).
    fn any_heap_sift_down<T: Element>() -> BinaryHeap<T> {
        let heap = any_heap();
        kani::assume(heap.len() <= MAX_SIFT_DOWN_LEN);
        heap
    }

    /// The end of a harness for `value`, which owns elements of type `T`: it is dropped,
    /// which frees its buffer, unless dropping an element has an effect (`DropFails`). In
    /// that case it is leaked: the element-wise drop of a vector of symbolic length is a
    /// loop without a bound, and outside the functions in scope.
    fn release<T, V>(value: V) {
        if mem::needs_drop::<T>() {
            mem::forget(value);
        } else {
            drop(value);
        }
    }

    /// The capacity that an empty vector of `T` grows to (`T` not zero-sized).
    fn min_cap<T>() -> usize {
        <crate::raw_vec::RawVec<T>>::MIN_NON_ZERO_CAP
    }

    /// Any slice: any length.
    fn any_slice<'a, T: Element + 'a>() -> &'a mut [T] {
        any_vec().leak()
    }

    /// A `PeekMut` in any state that safe code can reach: as returned by `peek_mut`, or
    /// after `deref_mut` (which shortens a longer heap to length 1 until the `PeekMut` is
    /// dropped). `deref` does not change the state and `refresh` returns to the first one.
    fn any_peek_mut<T: Element>(heap: &mut BinaryHeap<T>) -> Option<PeekMut<'_, T>> {
        let mut peek = heap.peek_mut()?;
        if kani::any() {
            let _: &mut T = &mut *peek;
        }
        Some(peek)
    }

    // ------------------------------------------------------------------------------------
    // `Hole`

    fn check_hole_new<T: Element>() {
        let data = any_slice::<T>();
        let (ptr, len) = (data.as_ptr(), data.len());
        let pos: usize = kani::any();
        // SAFETY: the precondition of the contract.
        let hole = unsafe { Hole::new(data, pos) };
        assert!(hole.pos == pos && hole.data.as_ptr() == ptr && hole.data.len() == len);
        kani::cover(len > 1_000_000 && pos == len - 1, "hole at the end of a long slice");
        kani::cover(pos == 0 && len == 1, "hole in a slice of one element");
        // `Drop for Hole` writes the element back.
    }

    fn check_hole_get<T: Element>() {
        let data = any_slice::<T>();
        let (ptr, len) = (data.as_ptr(), data.len());
        let pos: usize = kani::any_where(|pos: &usize| *pos < len);
        // SAFETY: `pos < len`.
        let hole = unsafe { Hole::new(data, pos) };
        let index: usize = kani::any();
        // SAFETY: the precondition of the contract.
        let elt: *const T = unsafe { hole.get(index) };
        assert!(elt == ptr.wrapping_add(index));
        kani::cover(len > 1_000_000 && index == len - 1, "last element of a long slice");
        kani::cover(index + 1 == pos, "element before the hole");
        kani::cover(index == pos + 1, "element after the hole");
    }

    fn check_hole_move_to<T: Element>() {
        let data = any_slice::<T>();
        let (ptr, len) = (data.as_ptr(), data.len());
        let pos: usize = kani::any_where(|pos: &usize| *pos < len);
        // SAFETY: `pos < len`.
        let mut hole = unsafe { Hole::new(data, pos) };
        let index: usize = kani::any();
        // SAFETY: the precondition of the contract.
        unsafe { hole.move_to(index) };
        assert!(hole.pos == index && hole.data.as_ptr() == ptr && hole.data.len() == len);
        kani::cover(len > 1_000_000 && pos == 0 && index == len - 1, "across a long slice");
        kani::cover(index + 1 == pos, "to the element before");
        kani::cover(index == pos + 1, "to the element after");
    }

    /// `Drop for Hole`, for a hole as created and for a hole that has moved.
    fn check_hole_drop<T: Element>() {
        let data = any_slice::<T>();
        let (ptr, len) = (data.as_ptr(), data.len());
        let pos: usize = kani::any_where(|pos: &usize| *pos < len);
        // SAFETY: `pos < len`.
        let mut hole = unsafe { Hole::new(data, pos) };
        let moved: bool = kani::any();
        if moved {
            let index: usize = kani::any_where(|index: &usize| *index != pos && *index < len);
            // SAFETY: `index` is in the slice and is not the hole.
            unsafe { hole.move_to(index) };
        }
        drop(hole);
        // The borrow of the slice is over, and the slice is the same one.
        assert!(data.as_ptr() == ptr && data.len() == len);
        kani::cover(moved && len > 1_000_000, "moved hole in a long slice");
        kani::cover(!moved && len == 1, "hole in a slice of one element");
    }

    // ------------------------------------------------------------------------------------
    // The sift functions

    fn check_sift_up<T: Element>() {
        let mut heap = any_heap::<T>();
        let len = heap.len();
        let start: usize = kani::any();
        let pos: usize = kani::any();
        // SAFETY: the precondition of the contract.
        let new_pos = unsafe { heap.sift_up(start, pos) };
        assert!(heap.len() == len);
        kani::cover(len > 1_000_000 && pos > 1_000 && new_pos < pos, "moved up in a long heap");
        kani::cover(new_pos == pos && pos > start, "stopped by the first comparison");
        kani::cover(new_pos == start && pos > start && pos - start > 1_000, "reached `start`");
        kani::cover(pos <= start, "no iteration");
        release::<T, _>(heap);
    }

    fn check_sift_down_range<T: Element>() {
        let mut heap = any_heap::<T>();
        let len = heap.len();
        let pos: usize = kani::any();
        // A longer range only exists in a heap of a zero-sized type, and a child index can
        // overflow in it: `panic_sift_down_range_child_index`.
        let end: usize = kani::any_where(|end: &usize| *end <= MAX_SIFT_DOWN_LEN);
        // SAFETY: the precondition of the contract.
        let new_pos = unsafe { heap.sift_down_range(pos, end) };
        assert!(heap.len() == len);
        kani::cover(new_pos > pos && new_pos - pos > 1_000, "moved far down");
        // `pos` has two children in the range.
        kani::cover(
            new_pos == pos && end >= 3 && pos <= (end - 3) / 2,
            "stopped by the first comparison",
        );
        kani::cover(new_pos == end - 1 && new_pos > pos, "moved to the last element");
        kani::cover(end == 1, "range of one element");
        kani::cover(end < len, "range shorter than the heap");
        release::<T, _>(heap);
    }

    fn check_sift_down<T: Element>() {
        let mut heap = any_heap_sift_down::<T>();
        let len = heap.len();
        let pos: usize = kani::any();
        // SAFETY: the precondition of the contract.
        let new_pos = unsafe { heap.sift_down(pos) };
        assert!(heap.len() == len);
        kani::cover(new_pos > pos && new_pos - pos > 1_000, "moved far down");
        // `pos` has two children.
        kani::cover(
            new_pos == pos && len >= 3 && pos <= (len - 3) / 2,
            "stopped by the first comparison",
        );
        kani::cover(len == 1, "heap of one element");
        release::<T, _>(heap);
    }

    fn check_sift_down_to_bottom<T: Element>() {
        let mut heap = any_heap_sift_down::<T>();
        let len = heap.len();
        let pos: usize = kani::any();
        // SAFETY: the precondition of the contract.
        unsafe { heap.sift_down_to_bottom(pos) };
        assert!(heap.len() == len);
        kani::cover(len > 1_000_000 && pos == 0, "from the root of a long heap");
        kani::cover(len > 1_000_000 && pos == len - 1, "from the last element of a long heap");
        kani::cover(len == 1, "heap of one element");
        kani::cover(len == 2 && pos == 0, "heap of two elements");
        release::<T, _>(heap);
    }

    // ------------------------------------------------------------------------------------
    // Safe functions

    fn check_push<T: Element>() {
        let mut heap = any_heap::<T>();
        let (len, cap) = (heap.len(), heap.capacity());
        // A longer vector does not exist (only reachable for a zero-sized type).
        kani::assume(len < usize::MAX);
        heap.push(kani::any());
        assert!(heap.len() == len + 1);
        kani::cover(len < cap && len > 1_000_000, "no reallocation, long heap");
        // A vector of a zero-sized type never allocates, but can be longer than `isize::MAX`.
        let zst = size_of::<T>() == 0;
        kani::cover(
            if zst { len > isize::MAX as usize } else { len == cap && len > 1_000_000 },
            "reallocation of a long heap (zero-sized: a heap longer than isize::MAX)",
        );
        // A sized vector grows from nothing to the minimum capacity for its element size:
        // 8, 4 or 1 elements (`raw_vec::min_non_zero_cap`).
        kani::cover(
            if zst { len == 0 } else { cap == 0 && heap.capacity() == min_cap::<T>() },
            "first element (sized: first allocation, of the minimum capacity)",
        );
        release::<T, _>(heap);
    }

    fn check_pop<T: Element>() {
        let mut heap = any_heap_sift_down::<T>();
        let len = heap.len();
        let item = heap.pop();
        assert!(item.is_some() == (len > 0));
        assert!(heap.len() == len.saturating_sub(1));
        kani::cover(len > 1_000_000, "long heap");
        kani::cover(len == 0, "empty heap");
        kani::cover(len == 1, "heap of one element");
        kani::cover(len == 2, "heap of two elements");
        release::<T, _>((item, heap));
    }

    fn check_peek_mut<T: Element>() {
        let mut heap = any_heap::<T>();
        let len = heap.len();
        let peek = heap.peek_mut();
        assert!(peek.is_some() == (len > 0));
        // Dropping a `PeekMut` that was never mutably dereferenced does nothing.
        drop(peek);
        assert!(heap.len() == len);
        kani::cover(len > 1_000_000, "long heap");
        kani::cover(len == 0, "empty heap");
        release::<T, _>(heap);
    }

    fn check_peek_mut_deref<T: Element>() {
        let mut heap = any_heap::<T>();
        let (ptr, len) = (heap.data.as_ptr(), heap.len());
        let Some(peek) = any_peek_mut(&mut heap) else {
            assert!(len == 0);
            return release::<T, _>(heap);
        };
        let amplified = peek.original_len.is_some();
        let top: *const T = &*peek;
        assert!(top == ptr);
        kani::cover(amplified && len > 1_000_000, "after `deref_mut`, long heap");
        kani::cover(!amplified && len > 1_000_000, "before `deref_mut`, long heap");
        kani::cover(len == 1, "heap of one element");
        // Leaked, so that this harness is only about `deref`.
        mem::forget(peek);
        release::<T, _>(heap);
    }

    /// `deref_mut`, then leak the `PeekMut`: the heap keeps the top element only, and is
    /// still a well-formed heap (same buffer and capacity, length 1), so everything that
    /// the other harnesses prove about any heap applies to it. `push`, `pop` and
    /// `peek_mut` are also run on it here.
    fn check_peek_mut_deref_mut_leak<T: Element>() {
        let mut heap = any_heap::<T>();
        let (ptr, len, cap) = (heap.data.as_ptr(), heap.len(), heap.capacity());
        let Some(mut peek) = any_peek_mut(&mut heap) else {
            assert!(len == 0);
            return release::<T, _>(heap);
        };
        let top: *mut T = &mut *peek;
        assert!(top as *const T == ptr);
        assert!(peek.heap.len() == 1);
        assert!(if len > 1 {
            peek.original_len == NonZero::new(len)
        } else {
            peek.original_len.is_none()
        });
        mem::forget(peek);

        assert!(heap.len() == 1 && heap.capacity() == cap && heap.data.as_ptr() == ptr);
        // `pop` comes before the pushes: after the loop of `sift_up` the elements are
        // arbitrary bytes to Kani (see "Models and limits"), and `item.is_some()` reads one.
        let item = heap.pop();
        assert!(item.is_some() && heap.is_empty() && heap.capacity() == cap);
        heap.push(kani::any());
        // This push reallocates if the capacity is 1.
        heap.push(kani::any());
        assert!(heap.len() == 2);
        let again = heap.peek_mut();
        assert!(again.is_some());
        drop(again);
        kani::cover(len > 1_000_000, "long heap, all but the top element leaked");
        kani::cover(len == 1, "heap of one element, nothing leaked");
        // A vector of a zero-sized type never allocates, but can be longer than `isize::MAX`.
        kani::cover(
            if size_of::<T>() == 0 { len > isize::MAX as usize } else { cap == 1 },
            "push after the leak reallocates (zero-sized: leak from a heap longer than isize::MAX)",
        );
        release::<T, _>(item);
        release::<T, _>(heap);
    }

    /// `Drop for PeekMut`.
    fn check_peek_mut_drop<T: Element>() {
        let mut heap = any_heap_sift_down::<T>();
        let len = heap.len();
        let Some(peek) = any_peek_mut(&mut heap) else {
            assert!(len == 0);
            return release::<T, _>(heap);
        };
        let amplified = peek.original_len.is_some();
        drop(peek);
        assert!(heap.len() == len);
        kani::cover(amplified && len > 1_000_000, "after `deref_mut`, long heap");
        kani::cover(!amplified && len > 1_000_000, "before `deref_mut`, long heap");
        kani::cover(len == 1, "heap of one element");
        release::<T, _>(heap);
    }

    fn check_peek_mut_pop<T: Element>() {
        let mut heap = any_heap_sift_down::<T>();
        let len = heap.len();
        let Some(peek) = any_peek_mut(&mut heap) else {
            assert!(len == 0);
            return release::<T, _>(heap);
        };
        let amplified = peek.original_len.is_some();
        let item = PeekMut::pop(peek);
        assert!(heap.len() == len - 1);
        kani::cover(amplified && len > 1_000_000, "after `deref_mut`, long heap");
        kani::cover(!amplified && len > 1_000_000, "before `deref_mut`, long heap");
        kani::cover(len == 1, "heap of one element");
        release::<T, _>(item);
        release::<T, _>(heap);
    }

    fn check_peek_mut_refresh<T: Element>() {
        let mut heap = any_heap_sift_down::<T>();
        let len = heap.len();
        let Some(mut peek) = any_peek_mut(&mut heap) else {
            assert!(len == 0);
            return release::<T, _>(heap);
        };
        let amplified = peek.original_len.is_some();
        let changed = peek.refresh();
        assert!(peek.original_len.is_none() && peek.heap.len() == len);
        assert!(amplified || !changed);
        // The refreshed `PeekMut` is usable again.
        let _: &mut T = &mut *peek;
        drop(peek);
        assert!(heap.len() == len);
        kani::cover(amplified && changed && len > 1_000_000, "top replaced, long heap");
        kani::cover(amplified && !changed && len > 1_000_000, "top unchanged, long heap");
        kani::cover(!amplified, "before `deref_mut`");
        release::<T, _>(heap);
    }

    fn check_rebuild<T: Element>() {
        let mut heap = any_heap_sift_down::<T>();
        let len = heap.len();
        heap.rebuild();
        assert!(heap.len() == len);
        kani::cover(len > 1_000_000, "long heap");
        kani::cover(len <= 1, "nothing to do");
        release::<T, _>(heap);
    }

    fn check_rebuild_tail<T: Element>() {
        let mut heap = any_heap::<T>();
        let len = heap.len();
        let start: usize = kani::any_where(|start: &usize| *start <= len);
        let tail_len = len - start;
        // Every input for which no arithmetic overflows. The others only exist for a
        // zero-sized type: the heuristic computes `2 * len` and `tail_len * 11` when the
        // tail is not longer than the rest, and `rebuild` computes child indices.
        kani::assume(if start == len {
            true
        } else if start < tail_len {
            len <= MAX_SIFT_DOWN_LEN
        } else {
            len <= usize::MAX / 2 && tail_len <= usize::MAX / 11
        });
        heap.rebuild_tail(start);
        assert!(heap.len() == len);
        kani::cover(start < tail_len && len > 1_000_000, "long tail: rebuild");
        // For a short heap the choice depends on `log2(start)`.
        let short = len <= 2048 && start >= tail_len && start < len;
        let log2_start = (usize::BITS - 1).saturating_sub(start.leading_zeros()) as usize;
        kani::cover(short && 2 * len < tail_len * log2_start, "short heap: rebuild");
        kani::cover(short && 2 * len >= tail_len * log2_start, "short heap: sift up");
        kani::cover(len > 1_000_000 && len - start == 1, "tail of one element: sift up");
        // For a long heap the choice depends on the length of the tail.
        let long = len > 1_000_000 && start >= tail_len && start < len;
        kani::cover(long && 2 * len < tail_len * 11, "long heap: rebuild");
        kani::cover(start == len, "empty tail");
        release::<T, _>(heap);
    }

    fn check_append<T: Element>() {
        let mut a = any_heap::<T>();
        let mut b = any_heap::<T>();
        let (len_a, len_b) = (a.len(), b.len());
        // The longer heap receives the shorter one.
        let cap_receiver = if len_a < len_b { b.capacity() } else { a.capacity() };
        // Every input without an overflow: the total length fits in a `usize` for
        // `Vec::append`, and `rebuild_tail` is called with a tail (the shorter heap) for
        // which its heuristic does not overflow (see `check_rebuild_tail`).
        let shorter = if len_a < len_b { len_a } else { len_b };
        kani::assume(len_a.checked_add(len_b).is_some_and(|total| {
            shorter == 0 || (total <= usize::MAX / 2 && shorter <= usize::MAX / 11)
        }));
        a.append(&mut b);
        assert!(a.len() == len_a + len_b && b.len() == 0);
        kani::cover(len_a < len_b && len_a > 1_000_000, "swapped, both long");
        kani::cover(len_a >= len_b && len_b > 1_000_000, "not swapped, both long");
        kani::cover(len_b == 0 && len_a > 0, "nothing to append");
        kani::cover(len_a == 0 && len_b == 0, "both empty");
        // A vector of a zero-sized type never allocates.
        let zst = size_of::<T>() == 0;
        kani::cover(
            if zst { len_a > 0 && len_b > 0 } else { a.capacity() > cap_receiver },
            "the receiving vector is reallocated (zero-sized: both heaps have elements)",
        );
        kani::cover(
            a.capacity() == cap_receiver && len_a > 0 && len_b > 0,
            "the receiving vector has room",
        );
        release::<T, _>((a, b));
    }

    fn check_into_sorted_vec<T: Element>() {
        let heap = any_heap_sift_down::<T>();
        let len = heap.len();
        let vec = heap.into_sorted_vec();
        assert!(vec.len() == len);
        kani::cover(len > 1_000_000, "long heap");
        kani::cover(len <= 1, "nothing to do");
        release::<T, _>(vec);
    }

    fn check_from_vec<T: Element>() {
        let vec = any_vec::<T>();
        let len = vec.len();
        kani::assume(len <= MAX_SIFT_DOWN_LEN);
        let heap = BinaryHeap::from(vec);
        assert!(heap.len() == len);
        kani::cover(len > 1_000_000, "long vector");
        kani::cover(len == 0, "empty vector");
        release::<T, _>(heap);
    }

    // ------------------------------------------------------------------------------------
    // The sorted iterators.
    //
    // `TrustedLen` requires `size_hint` to return the exact number of elements that the
    // iterator will yield. By induction on that number `n`: `size_hint` returns
    // `(n, Some(n))` with `n` the length of the heap; `next` returns `None` and leaves
    // the length at 0 if `n == 0`, and otherwise returns `Some` and leaves the length at
    // `n - 1`. So the iterator yields exactly `n` elements.

    fn check_into_iter_sorted<T: Element>() {
        let heap = any_heap_sift_down::<T>();
        let n = heap.len();
        let mut iter = heap.into_iter_sorted();
        assert!(iter.size_hint() == (n, Some(n)));
        let item = iter.next();
        assert!(item.is_some() == (n > 0));
        let m = iter.inner.len();
        assert!(m == n.saturating_sub(1));
        assert!(iter.size_hint() == (m, Some(m)));
        kani::cover(n > 1_000_000, "long heap");
        kani::cover(n == 0, "exhausted");
        kani::cover(n == 1, "last element");
        release::<T, _>((item, iter));
    }

    fn check_drain_sorted<T: Element>() {
        let mut heap = any_heap_sift_down::<T>();
        let n = heap.len();
        let mut iter = heap.drain_sorted();
        assert!(iter.size_hint() == (n, Some(n)));
        let item = iter.next();
        assert!(item.is_some() == (n > 0));
        let m = iter.inner.len();
        assert!(m == n.saturating_sub(1));
        assert!(iter.size_hint() == (m, Some(m)));
        kani::cover(n > 1_000_000, "long heap");
        kani::cover(n == 0, "exhausted");
        kani::cover(n == 1, "last element");
        // `Drop for DrainSorted` pops the remaining elements one by one; it is not in the
        // scope of the challenge. Leaking the iterator is safe and leaves the elements in
        // the heap.
        mem::forget(iter);
        assert!(heap.len() == m);
        release::<T, _>((item, heap));
    }

    // ------------------------------------------------------------------------------------
    // One set of harnesses per element type.

    /// The harnesses of the functions that access elements themselves.
    macro_rules! element_harnesses {
        ($t:ty) => {
            #[kani::proof_for_contract(Hole::<$t>::new)]
            fn hole_new() {
                check_hole_new::<$t>()
            }
            #[kani::proof_for_contract(Hole::<$t>::get)]
            fn hole_get() {
                check_hole_get::<$t>()
            }
            #[kani::proof_for_contract(Hole::<$t>::move_to)]
            fn hole_move_to() {
                check_hole_move_to::<$t>()
            }
            #[kani::proof]
            fn hole_drop() {
                check_hole_drop::<$t>()
            }
            #[kani::proof_for_contract(BinaryHeap::<$t>::sift_up)]
            fn sift_up() {
                check_sift_up::<$t>()
            }
            #[kani::proof_for_contract(BinaryHeap::<$t>::sift_down_range)]
            fn sift_down_range() {
                check_sift_down_range::<$t>()
            }
            #[kani::proof_for_contract(BinaryHeap::<$t>::sift_down)]
            fn sift_down() {
                check_sift_down::<$t>()
            }
            #[kani::proof_for_contract(BinaryHeap::<$t>::sift_down_to_bottom)]
            fn sift_down_to_bottom() {
                check_sift_down_to_bottom::<$t>()
            }
            #[kani::proof]
            fn push() {
                check_push::<$t>()
            }
            #[kani::proof]
            fn pop() {
                check_pop::<$t>()
            }
            #[kani::proof]
            fn peek_mut() {
                check_peek_mut::<$t>()
            }
            #[kani::proof]
            fn peek_mut_deref() {
                check_peek_mut_deref::<$t>()
            }
            #[kani::proof]
            fn peek_mut_deref_mut_leak() {
                check_peek_mut_deref_mut_leak::<$t>()
            }
            #[kani::proof]
            fn peek_mut_drop() {
                check_peek_mut_drop::<$t>()
            }
            #[kani::proof]
            fn peek_mut_pop() {
                check_peek_mut_pop::<$t>()
            }
            #[kani::proof]
            fn peek_mut_refresh() {
                check_peek_mut_refresh::<$t>()
            }
            #[kani::proof]
            fn into_iter_sorted() {
                check_into_iter_sorted::<$t>()
            }
            #[kani::proof]
            fn drain_sorted() {
                check_drain_sorted::<$t>()
            }
        };
    }

    /// The harnesses of the functions that reach elements only through the sift functions,
    /// `ptr::swap` and `Vec::append`.
    macro_rules! loop_harnesses {
        ($t:ty) => {
            #[kani::proof]
            fn rebuild() {
                check_rebuild::<$t>()
            }
            #[kani::proof]
            fn rebuild_tail() {
                check_rebuild_tail::<$t>()
            }
            #[kani::proof]
            fn append() {
                check_append::<$t>()
            }
            #[kani::proof]
            fn into_sorted_vec() {
                check_into_sorted_vec::<$t>()
            }
            #[kani::proof]
            fn from_vec() {
                check_from_vec::<$t>()
            }
        };
    }

    // Every harness, for these layouts: zero-sized; 1, 2, 4, 8 and 16 bytes, with alignment
    // 1 to 16; and 2 KiB, the last size class of `RawVec`'s growth (larger than 1 KiB).
    // When swapped (`pop`), they are whole words, or a tail of 4, 2 or 1 bytes. `bool`
    // (1 byte) has invalid bit patterns, `CellOrd` (8 bytes) has comparisons that overwrite
    // their operands, and `DropFails` (2 bytes) fails the proof if an element is dropped.
    mod t_zst {
        use super::*;
        element_harnesses!(AnyOrd<()>);
        loop_harnesses!(AnyOrd<()>);
    }
    mod t_u8 {
        use super::*;
        element_harnesses!(AnyOrd<u8>);
        loop_harnesses!(AnyOrd<u8>);
    }
    mod t_bool {
        use super::*;
        element_harnesses!(AnyOrd<bool>);
        loop_harnesses!(AnyOrd<bool>);
    }
    mod t_drop {
        use super::*;
        element_harnesses!(AnyOrd<DropFails>);
        loop_harnesses!(AnyOrd<DropFails>);
    }
    mod t_u32 {
        use super::*;
        element_harnesses!(AnyOrd<u32>);
        loop_harnesses!(AnyOrd<u32>);
    }
    mod t_u64 {
        use super::*;
        element_harnesses!(AnyOrd<u64>);
        loop_harnesses!(AnyOrd<u64>);
    }
    mod t_u128 {
        use super::*;
        element_harnesses!(AnyOrd<u128>);
        loop_harnesses!(AnyOrd<u128>);
    }
    mod t_cell {
        use super::*;
        element_harnesses!(CellOrd);
        loop_harnesses!(CellOrd);
    }
    mod t_big {
        use super::*;
        element_harnesses!(AnyOrd<[u64; 256]>);
        loop_harnesses!(AnyOrd<[u64; 256]>);
    }
    // Two more layouts, with sizes that are not a power of two, for the remaining paths of
    // `mem::swap`:
    //  * 6 bytes: swapped as a tail of 4 and 2 bytes, with no whole word;
    //  * 12 bytes, 3 of them padding: swapped as one word and a tail of 4 bytes.
    // They have the harnesses of the functions that access elements themselves. The other
    // five functions reach elements only through those, and through `ptr::swap` and
    // `Vec::append`, which have no branch that separates these sizes from 2, 4 or 16 bytes.
    // (With such sizes these five harnesses take several minutes to solve: byte offsets are
    // no longer shifts.)
    mod t_bytes6 {
        use super::*;
        element_harnesses!(AnyOrd<[u8; 6]>);
    }
    mod t_padded {
        use super::*;
        element_harnesses!(AnyOrd<Padded>);
    }

    // ------------------------------------------------------------------------------------
    // Panics. Each harness has one kind of input, which needs a heap that only exists for a
    // zero-sized type, or an argument that no caller passes. `should_panic` requires at
    // least one failed check, and every failed check to be a panic: some execution panics,
    // and no execution fails one of Kani's memory checks. The harnesses that end with
    // `must_have_panicked()` also show that every execution panics.

    /// A zero-sized element: a heap of these can be longer than `isize::MAX`.
    type Zst = AnyOrd<()>;

    /// The end of a harness in which every execution panics before this point. Kani reports
    /// reaching it as a failure that is not a panic, so the `should_panic` harness then
    /// fails: it passes only if no execution returns from the call under test.
    fn must_have_panicked() -> ! {
        // SAFETY: not reached in a harness that passes; Kani checks that.
        unsafe { core::hint::unreachable_unchecked() }
    }

    /// `2 * pos + 1` overflows for the position that `sift_down_range` starts from.
    #[kani::proof]
    #[kani::should_panic]
    fn panic_sift_down_range_child_index() {
        let mut heap = any_heap::<Zst>();
        let pos: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(pos > isize::MAX as usize && pos < end && end <= heap.len());
        // SAFETY: `pos < end <= heap.len()`.
        unsafe { heap.sift_down_range(pos, end) };
        must_have_panicked()
    }

    /// `2 * pos + 1` overflows for the position that `sift_down` starts from.
    #[kani::proof]
    #[kani::should_panic]
    fn panic_sift_down_child_index() {
        let mut heap = any_heap::<Zst>();
        let pos: usize = kani::any();
        kani::assume(pos > isize::MAX as usize && pos < heap.len());
        // SAFETY: `pos < heap.len()`.
        unsafe { heap.sift_down(pos) };
        must_have_panicked()
    }

    /// `2 * pos + 1` overflows for the position that `sift_down_to_bottom` starts from.
    #[kani::proof]
    #[kani::should_panic]
    fn panic_sift_down_to_bottom_child_index() {
        let mut heap = any_heap::<Zst>();
        let pos: usize = kani::any();
        kani::assume(pos > isize::MAX as usize && pos < heap.len());
        // SAFETY: `pos < heap.len()`.
        unsafe { heap.sift_down_to_bottom(pos) };
        must_have_panicked()
    }

    /// `pop` on a heap longer than `MAX_SIFT_DOWN_LEN + 1`: `2 * pos + 1` overflows once the
    /// hole is past `isize::MAX`. Whether it gets there depends on the comparisons, so some
    /// executions return.
    #[kani::proof]
    #[kani::should_panic]
    fn panic_pop_child_index() {
        let mut heap = any_heap::<Zst>();
        kani::assume(heap.len() > MAX_SIFT_DOWN_LEN + 1);
        let _ = heap.pop();
    }

    /// `push` on a full vector: capacity overflow.
    #[kani::proof]
    #[kani::should_panic]
    fn panic_push_full() {
        let mut heap = any_heap::<Zst>();
        kani::assume(heap.len() == usize::MAX);
        heap.push(kani::any());
        must_have_panicked()
    }

    /// `append` when the total length does not fit in a `usize`: capacity overflow.
    #[kani::proof]
    #[kani::should_panic]
    fn panic_append_too_long() {
        let mut a = any_heap::<Zst>();
        let mut b = any_heap::<Zst>();
        kani::assume(a.len().checked_add(b.len()).is_none());
        a.append(&mut b);
        must_have_panicked()
    }

    /// `rebuild_tail` with `start > len` (no caller does this): `len - start` overflows.
    #[kani::proof]
    #[kani::should_panic]
    fn panic_rebuild_tail_start_past_len() {
        let mut heap = any_heap::<AnyOrd<u8>>();
        let start: usize = kani::any();
        kani::assume(start > heap.len());
        heap.rebuild_tail(start);
        must_have_panicked()
    }

    /// Control for `DropFails`: a harness that does drop an element fails. (In the harnesses
    /// of `t_drop`, the same check passes: the destructor never runs.)
    #[kani::proof]
    #[kani::should_panic]
    fn panic_drop_fails_is_checked() {
        let mut heap = any_heap_sift_down::<AnyOrd<DropFails>>();
        kani::assume(heap.len() > 0);
        drop(heap.pop());
        must_have_panicked()
    }
}
