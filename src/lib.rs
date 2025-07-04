#![no_std]
#![cfg_attr(feature = "nightly_docs", feature(doc_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "rc")]
use alloc::rc::Rc;
#[cfg(feature = "alloc")]
use alloc::{boxed::Box, vec::Vec};
use core::cell::Cell;
use core::cell::UnsafeCell;
use core::ops::Index;
use core::ops::IndexMut;
use index::SliceCellIndex;

// TODO: decide whether &mut apis should in general return `&mut T` or `&mut Cell<T>`
// (or whether we need &mut apis at all, other than `as_mut(&mut self) -> &mut [T]`).
//
// Note: `Cell::get_mut` exists to go from `&mut Cell<T>` to `&mut T`.
//
// Currently, `split_first`/`split_last`/`.iter_mut` return `&mut T`, but
// `get_mut(usize)` returns `&mut Cell<T>`.

mod index;
#[cfg_attr(feature = "nightly_docs", doc(cfg(feature = "std")))]
#[cfg(feature = "std")]
pub mod io;

/// A [`Cell<[T; N]>`](core::cell::Cell)-like type that has some additional slice-like API.
///
/// This type dereferences to [`SliceCell<T>`](SliceCell).
///
/// This type can be converted to and from `Cell<[T; N]>` and `[Cell<T>; N]` in several ways.
#[repr(transparent)]
pub struct ArrayCell<T, const N: usize> {
    inner: UnsafeCell<[T; N]>,
}

// SAFETY: `Cell`-like types are safe to *send* between threads, but not to *share* between threads
// (so no `Sync` impl).
unsafe impl<T: Send, const N: usize> Send for ArrayCell<T, N> {}

/// A [`Cell<[T]>`](core::cell::Cell)-like type that has some additional slice-like API.
///
/// References to this type can be gotten from dereferencing an [`ArrayCell<T, N>`](ArrayCell), or using [`from_mut`](SliceCell::from_mut).
///
/// This type can be converted to and from `Cell<[T]>` and `[Cell<T>]` in several ways.
#[repr(transparent)]
pub struct SliceCell<T> {
    inner: UnsafeCell<[T]>,
}

// SAFETY: `Cell`-like types are safe to *send* between threads, but not to *share* between threads
// (so no `Sync` impl).
unsafe impl<T: Send> Send for SliceCell<T> {}

impl<T, const N: usize> ArrayCell<T, N> {
    /// View this [`ArrayCell`] as a [`Cell`] of an [array] of `N` elements.
    pub const fn as_std_ref(&self) -> &Cell<[T; N]> {
        // SAFETY: `Cell` upholds the same invariants that we do:
        // 1a. `Cell<T>` has the same layout as `T`.
        // 1b. `ArrayCell<T, N>` has the same layout as `[T; N]`.
        // 1c. `SliceCell<T>` has the same layout as `[T]`.
        // 2. `&Cell<T>` does not allow arbitrary user code to access `T` by reference directly.
        // Additional assumptions:
        // 3. `Cell<[T; N]>` has the same layout as `[Cell<T>; N]` (implied by 1).
        // This safety comment applies to the bodies of all `as_std_*`/`into_std_*` and `from_std_*` methods
        // on `SliceCell` and `ArrayCell`.
        unsafe { &*(self as *const Self).cast() }
    }
    /// View this [`ArrayCell`] as an [array] of `N` [`Cell`]s.
    pub const fn as_std_transposed_ref(&self) -> &[Cell<T>; N] {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &*(self as *const Self).cast() }
    }
    /// View a [`Cell`] of an [array] of `N` elements as an [`ArrayCell`].
    pub const fn from_std_ref(std: &Cell<[T; N]>) -> &Self {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &*(std as *const Cell<[T; N]>).cast() }
    }
    /// View an [array] of `N` [`Cell`]s as an [`ArrayCell`].
    pub const fn from_std_transposed_ref(std: &[Cell<T>; N]) -> &Self {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &*(std as *const [Cell<T>; N]).cast() }
    }
    /// View this [`ArrayCell`] as a [`Cell`] of an [array] of `N` elements.
    pub fn as_std_mut(&mut self) -> &mut Cell<[T; N]> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &mut *(self as *mut Self).cast() }
    }
    /// View this [`ArrayCell`] as an [array] of `N` [`Cell`]s.
    pub fn as_std_transposed_mut(&mut self) -> &mut [Cell<T>; N] {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &mut *(self as *mut Self).cast() }
    }
    /// View a [`Cell`] of an [array] of `N` elements as an [`ArrayCell`].
    pub fn from_std_mut(std: &mut Cell<[T; N]>) -> &mut Self {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &mut *(std as *mut Cell<[T; N]>).cast() }
    }
    /// View an [array] of `N` [`Cell`]s as an [`ArrayCell`].
    pub fn from_std_transposed_mut(std: &mut [Cell<T>; N]) -> &mut Self {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &mut *(std as *mut [Cell<T>; N]).cast() }
    }
}

#[cfg_attr(feature = "nightly_docs", doc(cfg(feature = "alloc")))]
#[cfg(feature = "alloc")]
impl<T, const N: usize> ArrayCell<T, N> {
    /// View this [`ArrayCell`] as a [`Cell`] of an [array] of `N` elements.
    pub fn into_std_boxed(self: Box<Self>) -> Box<Cell<[T; N]>> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Box::from_raw(Box::into_raw(self).cast()) }
    }
    /// View this [`ArrayCell`] as an [array] of `N` [`Cell`]s.
    pub fn into_std_transposed_boxed(self: Box<Self>) -> Box<[Cell<T>; N]> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Box::from_raw(Box::into_raw(self).cast()) }
    }
    /// View a [`Cell`] of an [array] of `N` elements as an [`ArrayCell`].
    pub fn from_std_boxed(std: Box<Cell<[T; N]>>) -> Box<Self> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Box::from_raw(Box::into_raw(std).cast()) }
    }
    /// View an [array] of `N` [`Cell`]s as an [`ArrayCell`].
    pub fn from_std_transposed_boxed(std: Box<[Cell<T>; N]>) -> Box<Self> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Box::from_raw(Box::into_raw(std).cast()) }
    }

    /// Wraps a [boxed](alloc::boxed::Box) [array] in an [`ArrayCell`].
    pub fn new_boxed(inner: Box<[T; N]>) -> Box<Self> {
        // SAFETY: `ArrayCell<T, N>` has the same layout as `[T; N]`.
        unsafe { Box::from_raw(Box::into_raw(inner).cast()) }
    }

    /// Unwaps a [boxed](alloc::boxed::Box) [ArrayCell] into an [array].
    pub fn into_inner_boxed(self: Box<Self>) -> Box<[T; N]> {
        // SAFETY: `ArrayCell<T, N>` has the same layout as `[T; N]`.
        unsafe { Box::from_raw(Box::into_raw(self).cast()) }
    }
}

#[cfg_attr(feature = "nightly_docs", doc(cfg(feature = "rc")))]
#[cfg(feature = "rc")]
impl<T, const N: usize> ArrayCell<T, N> {
    /// View this [`ArrayCell`] as a [`Cell`] of an [array] of `N` elements.
    pub fn into_std_rc(self: Rc<Self>) -> Rc<Cell<[T; N]>> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Rc::from_raw(Rc::into_raw(self).cast()) }
    }
    /// View this [`ArrayCell`] as an [array] of `N` [`Cell`]s.
    pub fn into_std_transposed_rc(self: Rc<Self>) -> Rc<[Cell<T>; N]> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Rc::from_raw(Rc::into_raw(self).cast()) }
    }
    /// View a [`Cell`] of an [array] of `N` elements as an [`ArrayCell`].
    pub fn from_std_rc(std: Rc<Cell<[T; N]>>) -> Rc<Self> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Rc::from_raw(Rc::into_raw(std).cast()) }
    }
    /// View an [array] of `N` [`Cell`]s as an [`ArrayCell`].
    pub fn from_std_transposed_rc(std: Rc<[Cell<T>; N]>) -> Rc<Self> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Rc::from_raw(Rc::into_raw(std).cast()) }
    }

    /// Wraps a [reference-counted](alloc::rc::Rc) [array] in an `ArrayCell`, if it is uniquely owned.
    pub fn try_new_rc(mut inner: Rc<[T; N]>) -> Result<Rc<Self>, Rc<[T; N]>> {
        match Rc::get_mut(&mut inner) {
            // SAFETY: `ArrayCell<T, N>` has the same layout as `[T; N]`.
            // And: there are no other `Rc` or `Weak` pointers to this allocation, so it is sound
            // to "add" interior mutability to it
            Some(_unique) => Ok(unsafe { Rc::from_raw(Rc::into_raw(inner).cast()) }),
            None => Err(inner),
        }
    }

    /// Unwraps a [reference-counted](alloc::rc::Rc) [`ArrayCell`] into an [array], if it is uniquely owned.
    pub fn try_into_inner_rc(mut self: Rc<Self>) -> Result<Rc<[T; N]>, Rc<Self>> {
        match Rc::get_mut(&mut self) {
            // SAFETY: `ArrayCell<T, N>` has the same layout as `[T; N]`.
            // And: there are no other `Rc` or `Weak` pointers to this allocation, so it is sound
            // to "remove" interior mutability from it
            Some(_unique) => Ok(unsafe { Rc::from_raw(Rc::into_raw(self).cast()) }),
            None => Err(self),
        }
    }

    /// Replacement for `From` impl, since `Rc` is not fundamental.
    // TODO: If manual coercion is added, just make ArrayCell<T, N> coerce to SliceCell<T>
    // and deprecate `ArrayCell::unsize_rc` (but not `SliceCell::try_size_rc`).
    pub fn unsize_rc(self: Rc<Self>) -> Rc<SliceCell<T>> {
        SliceCell::from_std_transposed_rc(ArrayCell::into_std_transposed_rc(self))
    }
}

impl<T, const N: usize> ArrayCell<T, N> {
    /// Returns a raw pointer to the underlying data in this [`ArrayCell`].
    pub fn as_ptr(&self) -> *mut [T; N] {
        UnsafeCell::raw_get(&self.inner).cast()
    }

    /// Consumes the [`ArrayCell`], returning the wrapped [array].
    pub fn into_inner(self) -> [T; N] {
        self.inner.into_inner()
    }

    /// Wraps an [array] in an [`ArrayCell`].
    pub fn new(inner: [T; N]) -> Self {
        Self {
            inner: UnsafeCell::new(inner),
        }
    }

    /// Unwraps a uniquely borrowed [`ArrayCell`] into an array.
    #[doc(alias = "get_mut")]
    pub fn as_mut(&mut self) -> &mut [T; N] {
        self.inner.get_mut()
    }

    /// Wraps a uniquely borrowed array in an [`ArrayCell`].
    pub fn from_mut(inner: &mut [T; N]) -> &mut Self {
        unsafe { &mut *(inner as *mut [T; N]).cast() }
    }

    /// Returns a reference to an element or subslice depending on the type of index.
    ///
    /// See [`slice::get`].
    pub fn get<I: SliceCellIndex<Self>>(&self, idx: I) -> Option<&I::Output> {
        idx.get(self)
    }

    /// Returns a mutable reference to an element or subslice depending on the type of index.
    ///
    /// See also [`slice::get_mut`].
    pub fn get_mut<I: SliceCellIndex<Self>>(&mut self, idx: I) -> Option<&mut I::Output> {
        idx.get_mut(self)
    }

    /// Returns the length of the [`ArrayCell`].
    pub const fn len(&self) -> usize {
        N
    }
}

impl<T, const N: usize> AsRef<SliceCell<T>> for ArrayCell<T, N> {
    fn as_ref(&self) -> &SliceCell<T> {
        SliceCell::from_std_ref(self.as_std_ref())
    }
}

impl<T, const N: usize> AsMut<SliceCell<T>> for ArrayCell<T, N> {
    fn as_mut(&mut self) -> &mut SliceCell<T> {
        SliceCell::from_mut(self.as_mut())
    }
}

impl<T> AsRef<SliceCell<T>> for SliceCell<T> {
    fn as_ref(&self) -> &SliceCell<T> {
        self
    }
}

impl<T> AsMut<SliceCell<T>> for SliceCell<T> {
    fn as_mut(&mut self) -> &mut SliceCell<T> {
        self
    }
}

impl<T> SliceCell<T> {
    /// View this [`SliceCell`] as a [`Cell`] of a [slice].
    pub const fn as_std_ref(&self) -> &Cell<[T]> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &*(self as *const Self as *const _) }
    }
    /// View this [`SliceCell`] as a [slice] of [`Cell`]s.
    pub const fn as_std_transposed_ref(&self) -> &[Cell<T>] {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &*(self as *const Self as *const _) }
    }
    /// View a [`Cell`] of a [slice] as a [`SliceCell`].
    pub const fn from_std_ref(std: &Cell<[T]>) -> &Self {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &*(std as *const Cell<[T]> as *const _) }
    }
    /// View a [slice] of [`Cell`]s as a [`SliceCell`].
    pub const fn from_std_transposed_ref(std: &[Cell<T>]) -> &Self {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &*(std as *const [Cell<T>] as *const _) }
    }
    /// View this [`SliceCell`] as a [`Cell`] of a [slice].
    pub fn as_std_mut(&mut self) -> &mut Cell<[T]> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &mut *(self as *mut Self as *mut _) }
    }
    /// View this [`SliceCell`] as a [slice] of [`Cell`]s.
    pub fn as_std_transposed_mut(&mut self) -> &mut [Cell<T>] {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &mut *(self as *mut Self as *mut _) }
    }
    /// View a [`Cell`] of a [slice] as a [`SliceCell`].
    pub fn from_std_mut(std: &mut Cell<[T]>) -> &mut Self {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &mut *(std as *mut Cell<[T]> as *mut _) }
    }
    /// View a [slice] of [`Cell`] as a [`SliceCell`].
    pub fn from_std_transposed_mut(std: &mut [Cell<T>]) -> &mut Self {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { &mut *(std as *mut [Cell<T>] as *mut _) }
    }
}

#[cfg(feature = "alloc")]
impl<T> SliceCell<T> {
    /// View this [`SliceCell`] as a [`Cell`] of a [slice].
    pub fn into_std_boxed(self: Box<Self>) -> Box<Cell<[T]>> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Box::from_raw(Box::into_raw(self) as *mut _) }
    }
    /// View this [`SliceCell`] as a [slice] of [`Cell`]s.
    pub fn into_std_transposed_boxed(self: Box<Self>) -> Box<[Cell<T>]> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Box::from_raw(Box::into_raw(self) as *mut _) }
    }
    /// View a [`Cell`] of a [slice] as a [`SliceCell`].
    pub fn from_std_boxed(std: Box<Cell<[T]>>) -> Box<Self> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Box::from_raw(Box::into_raw(std) as *mut _) }
    }
    /// View a [slice] of [`Cell`]s as a [`SliceCell`].
    pub fn from_std_transposed_boxed(std: Box<[Cell<T>]>) -> Box<Self> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Box::from_raw(Box::into_raw(std) as *mut _) }
    }

    /// Unwraps an owned [boxed](alloc::boxed::Box) [`SliceCell`] into a slice.
    pub fn into_inner_boxed(self: Box<Self>) -> Box<[T]> {
        // SAFETY: `ArrayCell<T, N>` has the same layout as `[T; N]`.
        unsafe { Box::from_raw(Box::into_raw(self) as *mut _) }
    }

    /// Wraps an owned [boxed](alloc::boxed::Box) [slice] in a [`SliceCell`].
    pub fn new_boxed(inner: Box<[T]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(inner) as *mut _) }
    }
}

#[cfg(feature = "rc")]
impl<T> SliceCell<T> {
    /// View this [`SliceCell`] as a [`Cell`] of a [slice].
    pub fn into_std_rc(self: Rc<Self>) -> Rc<Cell<[T]>> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Rc::from_raw(Rc::into_raw(self) as *const _) }
    }
    /// View this [`SliceCell`] as a [slice] of [`Cell`]s.
    pub fn into_std_transposed_rc(self: Rc<Self>) -> Rc<[Cell<T>]> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Rc::from_raw(Rc::into_raw(self) as *const _) }
    }
    /// View a [`Cell`] of a [slice] as a [`SliceCell`].
    pub fn from_std_rc(std: Rc<Cell<[T]>>) -> Rc<Self> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Rc::from_raw(Rc::into_raw(std) as *const _) }
    }
    pub fn from_std_transposed_rc(std: Rc<[Cell<T>]>) -> Rc<Self> {
        // See `ArrayCell::as_std_ref` for safety.
        unsafe { Rc::from_raw(Rc::into_raw(std) as *const _) }
    }

    /// Wraps a [reference-counted](alloc::rc::Rc) [slice] in a `SliceCell`, if it is uniquely owned.
    pub fn try_new_rc(mut inner: Rc<[T]>) -> Result<Rc<Self>, Rc<[T]>> {
        match Rc::get_mut(&mut inner) {
            // SAFETY: `SliceCell<T>` has the same layout as `[T]`.
            // And: there are no other `Rc` or `Weak` pointers to this allocation, so it is sound
            // to "add" interior mutability to it
            Some(_unique) => Ok(unsafe { Rc::from_raw(Rc::into_raw(inner) as *const _) }),
            None => Err(inner),
        }
    }

    /// Unwraps a [reference-counted](alloc::rc::Rc) [`SliceCell`] into an [slice], if it is uniquely owned.
    pub fn try_into_inner_rc(mut self: Rc<Self>) -> Result<Rc<[T]>, Rc<Self>> {
        match Rc::get_mut(&mut self) {
            // SAFETY: `SliceCell<T>` has the same layout as `[T]`.
            // And: there are no other `Rc` or `Weak` pointers to this allocation, so it is sound
            // to "remove" interior mutability from it
            Some(_unique) => Ok(unsafe { Rc::from_raw(Rc::into_raw(self) as *const _) }),
            None => Err(self),
        }
    }

    /// Replacement for `TryFrom` impl, since `Rc` is not fundamental
    pub fn try_size_rc<const N: usize>(self: Rc<Self>) -> Result<Rc<ArrayCell<T, N>>, Rc<Self>> {
        if self.len() == N {
            Ok({
                let the_rc = self
                    .into_std_transposed_rc()
                    .try_into()
                    .ok()
                    .expect("already checked the length");
                ArrayCell::from_std_transposed_rc(the_rc)
            })
        } else {
            Err(self)
        }
    }
}

impl<T> SliceCell<T> {
    /// Returns a raw pointer to the underlying data in this `SliceCell`.
    pub fn as_ptr(&self) -> *mut [T] {
        UnsafeCell::raw_get(&self.inner)
    }

    /// Unwraps a uniquely borrowed [`SliceCell`] into a slice.
    #[doc(alias = "get_mut")]
    pub fn as_mut(&mut self) -> &mut [T] {
        self.inner.get_mut()
    }

    /// Wraps a uniquely borrowed slice in a [`SliceCell`].
    pub fn from_mut(inner: &mut [T]) -> &mut Self {
        // SAFETY: `SliceCell<T>` has the same layout as `[T]`.
        // And: the slice is uniquely borrowed, so it is sound to "add" interior mutability for the
        // length of the borrow.
        unsafe { &mut *(inner as *mut [T] as *mut _) }
    }

    /// Returns a reference to an element or subslice depending on the type of index.
    ///
    /// See [`slice::get`].
    pub fn get<I: SliceCellIndex<Self>>(&self, idx: I) -> Option<&I::Output> {
        idx.get(self)
    }

    /// Returns a mutable reference to an element or subslice depending on the type of index.
    ///
    /// See also [`slice::get_mut`].
    pub fn get_mut<I: SliceCellIndex<Self>>(&mut self, idx: I) -> Option<&mut I::Output> {
        idx.get_mut(self)
    }

    /// Returns the length of the [`SliceCell`].
    pub const fn len(&self) -> usize {
        self.as_std_transposed_ref().len()
    }

    /// Divide one `SliceCell` into two at an index.
    ///
    /// Panics if `mid > self.len()`.
    ///
    /// See [slice::split_at]
    pub fn split_at(&self, mid: usize) -> (&SliceCell<T>, &SliceCell<T>) {
        let (start, end) = self.as_std_transposed_ref().split_at(mid);
        (
            Self::from_std_transposed_ref(start),
            Self::from_std_transposed_ref(end),
        )
    }

    /// Divide one mutable `SliceCell` into two at an index.
    ///
    /// Panics if `mid > self.len()`.
    ///
    /// See [slice::split_at_mut]
    pub fn split_at_mut(&mut self, mid: usize) -> (&mut SliceCell<T>, &mut SliceCell<T>) {
        let (start, end) = self.as_mut().split_at_mut(mid);
        (Self::from_mut(start), Self::from_mut(end))
    }

    /// Returns the first and all the rest of the elements of the `SliceCell`, or None if it is empty.
    ///
    /// See [slice::split_first]
    pub fn split_first(&self) -> Option<(&Cell<T>, &SliceCell<T>)> {
        let (first, end) = self.as_std_transposed_ref().split_first()?;
        Some((first, Self::from_std_transposed_ref(end)))
    }

    /// Returns the first and all the rest of the elements of the `SliceCell`, or None if it is empty.
    ///
    /// See [slice::split_first_mut]
    pub fn split_first_mut(&mut self) -> Option<(&mut T, &mut SliceCell<T>)> {
        let (first, end) = self.as_mut().split_first_mut()?;
        Some((first, Self::from_mut(end)))
    }

    /// Returns the last and all the rest of the elements of the `SliceCell`, or None if it is empty.
    ///
    /// See [slice::split_last]
    pub fn split_last(&self) -> Option<(&Cell<T>, &SliceCell<T>)> {
        let (last, start) = self.as_std_transposed_ref().split_last()?;
        Some((last, Self::from_std_transposed_ref(start)))
    }

    /// Returns the last and all the rest of the elements of the `SliceCell`, or None if it is empty.
    ///
    /// See [slice::split_last_mut]
    pub fn split_last_mut(&mut self) -> Option<(&mut T, &mut SliceCell<T>)> {
        let (last, start) = self.as_mut().split_last_mut()?;
        Some((last, Self::from_mut(start)))
    }

    /// Copies all elements from src into self, likely using a memcpy.
    ///
    /// The length of src must be the same as self.
    ///
    /// See [slice::copy_from_slice].
    pub fn copy_from_slice(&self, src: &[T])
    where
        T: Copy,
    {
        assert!(self.len() == src.len());
        // Compiles down to a memcpy in release mode, at least on 1.66.0
        self.iter().zip(src.iter()).for_each(|(dst, src)| {
            dst.set(*src);
        });
    }

    /// Copies all elements from src into self, likely using a memmove.
    ///
    /// The length of src must be the same as self.
    ///
    /// `self` and `src` may overlap.
    pub fn copy_from(&self, src: &SliceCell<T>)
    where
        T: Copy,
    {
        assert!(self.len() == src.len());
        // SAFETY: *src and *self may overlap, but that's fine since std::ptr::copy is
        // a memmove, not a memcpy. Both are valid for `self.len() * size_of::<T>()` bytes
        // for read/write, since their lengths are the same.
        unsafe {
            std::ptr::copy(
                src.as_ptr() as *const T,
                self.as_ptr() as *mut T,
                self.len(),
            );
        }
    }

    /// Clones all elements from src into self.
    ///
    /// The length of src must be the same as self.
    ///
    /// See [slice::copy_from_slice].
    pub fn clone_from_slice(&self, src: &[T])
    where
        T: Clone,
    {
        assert!(self.len() == src.len());
        // T::clone and T::drop are arbitrary user code, so we can't use `self.inner.get().clone_from_slice()`
        for (dst, val) in self.iter().zip(src.iter().cloned()) {
            dst.set(val);
        }
    }

    /// Take all elements from this `SliceCell` into a mutable slice, leaving `T::default()` in each cell
    pub fn take_into_slice(&self, dst: &mut [T])
    where
        T: Default,
    {
        assert!(self.len() == dst.len());
        // T::default and T::drop are arbitrary user code, so we can't hold a reference into self while it runs.
        for (src, dst) in self.iter().zip(dst.iter_mut()) {
            let val = src.take();
            *dst = val;
        }
    }

    /// Take all elements from this `SliceCell` into a newly allocated `Vec<T>`, leaving `T::default()` in each cell.
    #[cfg_attr(feature = "nightly_docs", doc(cfg(feature = "alloc")))]
    #[cfg(feature = "alloc")]
    pub fn take_into_vec(&self) -> Vec<T>
    where
        T: Default,
    {
        self.iter().map(Cell::take).collect()
    }

    /// Copy all elements from this `SliceCell` into a mutable slice.
    pub fn copy_into_slice(&self, dst: &mut [T])
    where
        T: Copy,
    {
        assert!(self.len() == dst.len());
        // Compiles down to a memcpy in release mode, at least on 1.66.0
        self.iter().zip(dst.iter_mut()).for_each(|(src, dst)| {
            *dst = src.get();
        });
    }

    /// Copy all elements from this `SliceCell` into a newly allocated `Vec<T>`.
    #[cfg_attr(feature = "nightly_docs", doc(cfg(feature = "alloc")))]
    #[cfg(feature = "alloc")]
    pub fn copy_into_vec(&self) -> Vec<T>
    where
        T: Copy,
    {
        // Compiles down to a memcpy in release mode, at least on 1.66.0
        self.iter().map(Cell::get).collect()
    }

    #[cfg_attr(feature = "nightly_docs", doc(cfg(feature = "alloc")))]
    #[cfg(feature = "alloc")]
    pub fn replace_with_vec(&self, mut src: Vec<T>) {
        self.swap_with_slice(&mut src);
    }

    pub fn swap_with_slice(&self, val: &mut [T]) {
        assert_eq!(self.len(), val.len());
        // SAFETY: (assumes that) `slice::swap_with_slice` uses memcpy-like operations,
        // and does not run arbitrary user code that could access `*self` racily
        unsafe { &mut *self.inner.get() }.swap_with_slice(val);
    }

    #[cfg(any())]
    pub fn swap_with_slicecell(&self, other: &Self) -> Result {
        todo!("decide what to do with overlapping slices. Probably just return an error?")
    }

    /// Swaps two elements in the slice.
    ///
    /// See [`<[T]>::swap`](slice::swap).
    pub fn swap(&self, a: usize, b: usize) {
        if a == b {
            return;
        }
        let a = &self[a];
        let b = &self[b];
        Cell::swap(a, b)
    }

    /// See [`<[T]>::rotate_left`](slice::rotate_left)
    pub fn rotate_left(&self, mid: usize) {
        // SAFETY: (assumes that) `slice::rotate_right` uses memcpy-like operations,
        // and does not run arbitrary user code that could access `*self` racily
        unsafe { &mut *self.inner.get() }.rotate_left(mid)
    }

    /// See [`<[T]>::rotate_right`](slice::rotate_right)
    pub fn rotate_right(&self, mid: usize) {
        // SAFETY: (assumes that) `slice::rotate_right` uses memcpy-like operations,
        // and does not run arbitrary user code that could access `*self` racily
        unsafe { &mut *self.inner.get() }.rotate_right(mid)
    }

    /// Fills self with elements by cloning value.
    ///
    /// See also: [`<[T]>::fill`](slice::fill).
    pub fn fill(&self, val: T)
    where
        T: Clone,
    {
        for dst in self {
            dst.set(val.clone());
        }
    }

    /// Fills self with elements returned by calling a closure repeatedly.
    ///
    /// See also: [`<[T]>::fill_with`](slice::fill_with).
    pub fn fill_with<F>(&self, mut f: F)
    where
        F: FnMut() -> T,
    {
        for dst in self {
            dst.set(f());
        }
    }

    /// N should not be 0.
    ///
    /// Splits the slice into a slice of N-element arrays, starting at the beginning of the slice, and a remainder slice with length strictly less than N.
    pub fn as_chunks<const N: usize>(&self) -> (&SliceCell<[T; N]>, &Self) {
        if N == 0 {
            (Default::default(), self)
        } else {
            let chunk_count = self.len() / N;
            let remainder = self.len() % N;
            let (chunks, remainder) = self.split_at(self.len() - remainder);
            let chunks: &[Cell<T>] = chunks.as_std_transposed_ref();
            // SAFETY: [[T; N]] has the same layout as [T], Cell<T> has the same layout as T
            // (so [Cell<T>] => [[Cell<T>; N]] => [Cell<[T; N]>]),
            // and we calculated the correct length.
            let chunks: &[Cell<[T; N]>] =
                unsafe { core::slice::from_raw_parts(chunks.as_ptr().cast(), chunk_count) };
            let chunks: &SliceCell<[T; N]> = SliceCell::from_std_transposed_ref(chunks);
            (chunks, remainder)
        }
    }

    /// N should not be 0.
    ///
    /// Splits the slice into a slice of N-element arrays, starting at the end of the slice, and a remainder slice with length strictly less than N.
    pub fn as_rchunks<const N: usize>(&self) -> (&Self, &SliceCell<[T; N]>) {
        if N == 0 {
            (self, Default::default())
        } else {
            let chunk_count = self.len() / N;
            let remainder = self.len() % N;
            let (remainder, chunks) = self.split_at(remainder);
            let chunks: &[Cell<T>] = chunks.as_std_transposed_ref();
            // SAFETY: [[T; N]] has the same layout as [T], Cell<T> has the same layout as T
            // (so [Cell<T>] => [[Cell<T>; N]] => [Cell<[T; N]>]),
            // and we calculated the correct length.
            let chunks: &[Cell<[T; N]>] =
                unsafe { core::slice::from_raw_parts(chunks.as_ptr().cast(), chunk_count) };
            let chunks: &SliceCell<[T; N]> = SliceCell::from_std_transposed_ref(chunks);
            (remainder, chunks)
        }
    }

    /// N should not be 0.
    ///
    /// Splits the slice into a slice of N-element arrays, starting at the beginning of the slice, and a remainder slice with length strictly less than N.
    pub fn as_chunks_mut<const N: usize>(&mut self) -> (&mut SliceCell<[T; N]>, &mut Self) {
        if N == 0 {
            (Default::default(), self)
        } else {
            let chunk_count = self.len() / N;
            let remainder = self.len() % N;
            let (chunks, remainder) = self.split_at_mut(self.len() - remainder);
            let chunks: &mut [T] = chunks.as_mut();
            // SAFETY: [[T; N]] has the same layout as [T], and we calculated the correct length.
            let chunks: &mut [[T; N]] =
                unsafe { core::slice::from_raw_parts_mut(chunks.as_mut_ptr().cast(), chunk_count) };
            let chunks: &mut SliceCell<[T; N]> = SliceCell::from_mut(chunks);
            (chunks, remainder)
        }
    }

    /// N should not be 0.
    ///
    /// Splits the slice into a slice of N-element arrays, starting at the end of the slice, and a remainder slice with length strictly less than N.
    pub fn as_rchunks_mut<const N: usize>(&mut self) -> (&mut Self, &mut SliceCell<[T; N]>) {
        if N == 0 {
            (self, Default::default())
        } else {
            let chunk_count = self.len() / N;
            let remainder = self.len() % N;
            let (remainder, chunks) = self.split_at_mut(remainder);
            let chunks: &mut [T] = chunks.as_mut();
            // SAFETY: [[T; N]] has the same layout as [T], and we calculated the correct length.
            let chunks: &mut [[T; N]] =
                unsafe { core::slice::from_raw_parts_mut(chunks.as_mut_ptr().cast(), chunk_count) };
            let chunks: &mut SliceCell<[T; N]> = SliceCell::from_mut(chunks);
            (remainder, chunks)
        }
    }

    pub fn iter(&self) -> core::slice::Iter<'_, Cell<T>> {
        IntoIterator::into_iter(self)
    }

    pub fn iter_mut(&mut self) -> core::slice::IterMut<'_, T> {
        self.as_mut().iter_mut()
    }
}

impl<T, const N: usize> SliceCell<[T; N]> {
    /// Flattens a `&SliceCell<[T; N]>` into a `&SliceCell<T>`.
    ///
    /// # Panics
    ///
    /// Panics if the length of the resulting `SliceCell` would overflow a `usize`.
    ///
    /// See also [`slice::flatten`].
    pub fn flatten(&self) -> &SliceCell<T> {
        let new_len = self.len().checked_mul(N).expect("length overflow");
        let this: &[Cell<[T; N]>] = self.as_std_transposed_ref();
        // SAFETY: [[T; N]] has the same layout as [T], Cell<T> has the same layout as T
        // (so [Cell<[T; N]>] => [[Cell<T>; N]] => [Cell<T>]),
        // and we calculated the correct length.
        let this: &[Cell<T>] =
            unsafe { core::slice::from_raw_parts(this.as_ptr().cast(), new_len) };
        let this: &SliceCell<T> = SliceCell::from_std_transposed_ref(this);
        this
    }

    /// Flattens a `&mut SliceCell<[T; N]>` into a `&mut SliceCell<T>`.
    ///
    /// # Panics
    ///
    /// Panics if the length of the resulting `SliceCell` would overflow a `usize`.
    ///
    /// See also [`slice::flatten_mut`].
    pub fn flatten_mut(&mut self) -> &mut SliceCell<T> {
        let new_len = self.len().checked_mul(N).expect("length overflow");
        let this: &mut [[T; N]] = self.as_mut();
        // SAFETY: [[T; N]] has the same layout as [T], and we calculated the correct length.
        let this: &mut [T] =
            unsafe { core::slice::from_raw_parts_mut(this.as_mut_ptr().cast(), new_len) };
        let this: &mut SliceCell<T> = SliceCell::from_mut(this);
        this
    }

    /// Access this `SliceCell` of [array]s as a [slice] of [`ArrayCell`]s.
    #[cfg(any())]
    pub fn as_slice_of_arraycells(&self) -> &[ArrayCell<T, N>] {
        todo!()
    }
}

impl<T, I: SliceCellIndex<Self>> Index<I> for SliceCell<T> {
    type Output = <I as SliceCellIndex<Self>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        index.get(self).unwrap()
    }
}

impl<T, I: SliceCellIndex<Self>> IndexMut<I> for SliceCell<T> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        index.get_mut(self).unwrap()
    }
}

impl<'a, T: 'a> Default for &'a mut ArrayCell<T, 0> {
    fn default() -> Self {
        ArrayCell::from_mut(&mut [])
    }
}

impl<'a, T: 'a> Default for &'a ArrayCell<T, 0> {
    fn default() -> Self {
        ArrayCell::from_mut(&mut [])
    }
}

impl<'a, T: 'a> Default for &'a mut SliceCell<T> {
    fn default() -> Self {
        SliceCell::from_mut(&mut [])
    }
}

impl<'a, T: 'a> Default for &'a SliceCell<T> {
    fn default() -> Self {
        SliceCell::from_mut(&mut [])
    }
}

impl<'a, T, const N: usize> From<&'a ArrayCell<T, N>> for &'a SliceCell<T> {
    fn from(value: &'a ArrayCell<T, N>) -> Self {
        SliceCell::from_std_ref(value.as_std_ref())
    }
}

impl<'a, T, const N: usize> From<&'a mut ArrayCell<T, N>> for &'a mut SliceCell<T> {
    fn from(value: &'a mut ArrayCell<T, N>) -> Self {
        SliceCell::from_mut(value.as_mut())
    }
}

#[cfg_attr(feature = "nightly_docs", doc(cfg(feature = "alloc")))]
#[cfg(feature = "alloc")]
impl<'a, T, const N: usize> From<Box<ArrayCell<T, N>>> for Box<SliceCell<T>> {
    fn from(value: Box<ArrayCell<T, N>>) -> Self {
        SliceCell::from_std_boxed(value.into_std_boxed())
    }
}

impl<'a, T, const N: usize> TryFrom<&'a SliceCell<T>> for &'a ArrayCell<T, N> {
    type Error = &'a SliceCell<T>;

    fn try_from(value: &'a SliceCell<T>) -> Result<Self, Self::Error> {
        if value.len() == N {
            Ok({
                let the_ref = value
                    .as_std_transposed_ref()
                    .try_into()
                    .expect("already checked the length");
                ArrayCell::from_std_transposed_ref(the_ref)
            })
        } else {
            Err(value)
        }
    }
}

impl<'a, T, const N: usize> TryFrom<&'a mut SliceCell<T>> for &'a mut ArrayCell<T, N> {
    type Error = &'a mut SliceCell<T>;

    fn try_from(value: &'a mut SliceCell<T>) -> Result<Self, Self::Error> {
        if value.len() == N {
            Ok({
                let the_mut = value
                    .as_mut()
                    .try_into()
                    .expect("already checked the length");
                ArrayCell::from_mut(the_mut)
            })
        } else {
            Err(value)
        }
    }
}

#[cfg_attr(feature = "nightly_docs", doc(cfg(feature = "alloc")))]
#[cfg(feature = "alloc")]
impl<'a, T, const N: usize> TryFrom<Box<SliceCell<T>>> for Box<ArrayCell<T, N>> {
    type Error = Box<SliceCell<T>>;

    fn try_from(value: Box<SliceCell<T>>) -> Result<Self, Self::Error> {
        if value.len() == N {
            Ok({
                let the_box = value
                    .into_std_transposed_boxed()
                    .try_into()
                    .ok()
                    .expect("already checked the length");
                ArrayCell::from_std_transposed_boxed(the_box)
            })
        } else {
            Err(value)
        }
    }
}

impl<'a, T> IntoIterator for &'a SliceCell<T> {
    type Item = &'a Cell<T>;

    type IntoIter = core::slice::Iter<'a, Cell<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_std_transposed_ref().iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a ArrayCell<T, N> {
    type Item = &'a Cell<T>;

    type IntoIter = core::slice::Iter<'a, Cell<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_std_transposed_ref().iter()
    }
}

impl<'a, T> IntoIterator for &'a mut SliceCell<T> {
    type Item = &'a mut T;

    type IntoIter = core::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_mut().iter_mut()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut ArrayCell<T, N> {
    type Item = &'a mut T;

    type IntoIter = core::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_mut().iter_mut()
    }
}
