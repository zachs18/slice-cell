#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "rc")]
use alloc::rc::Rc;
#[cfg(feature = "alloc")]
use alloc::{boxed::Box, vec::Vec};
#[cfg(feature = "assume_cell_layout")]
use core::cell::Cell;
use core::cell::UnsafeCell;
use core::ops::Deref;
use core::ops::DerefMut;
use core::ops::Index;
use core::ops::IndexMut;
use index::SliceCellIndex;

mod index;
#[cfg(feature = "std")]
pub mod io;

/// A [`Cell<[T; N]>`](core::cell::Cell)-like type that has some additional slice-like API.
///
/// This type dereferences to [`SliceCell<T>`](SliceCell).
///
/// Under the `assume_cell_layout` cargo feature, this type can be converted to and from `Cell<[T; N]>` and `[Cell<T>; N]` in several ways.
#[repr(transparent)]
pub struct ArrayCell<T, const N: usize> {
    inner: UnsafeCell<[T; N]>,
}

/// A [`Cell<[T]>`](core::cell::Cell)-like type that has some additional slice-like API.
///
/// References to this type can be gotten from dereferencing an [`ArrayCell<T, N>`](ArrayCell), or using [`from_mut`](SliceCell::from_mut).
///
/// Under the `assume_cell_layout` cargo feature, this type can be converted to and from `Cell<[T]>` and `[Cell<T>]` in several ways.
#[repr(transparent)]
pub struct SliceCell<T> {
    inner: UnsafeCell<[T]>,
}

#[cfg(feature = "assume_cell_layout")]
impl<T, const N: usize> ArrayCell<T, N> {
    /// View this [`ArrayCell`] as a [`Cell`] of an [array] of `N` elements.
    pub fn as_std_ref(&self) -> &Cell<[T; N]> {
        unsafe { &*(self as *const Self).cast() }
    }
    /// View this [`ArrayCell`] as an [array] of `N` [`Cell`]s.
    pub fn as_std_transposed_ref(&self) -> &[Cell<T>; N] {
        unsafe { &*(self as *const Self).cast() }
    }
    /// View a [`Cell`] of an [array] of `N` elements as an [`ArrayCell`].
    pub fn from_std_ref(std: &Cell<[T; N]>) -> &Self {
        unsafe { &*(std as *const Cell<[T; N]>).cast() }
    }
    /// View an [array] of `N` [`Cell`]s as an [`ArrayCell`].
    pub fn from_std_transposed_ref(std: &[Cell<T>; N]) -> &Self {
        unsafe { &*(std as *const [Cell<T>; N]).cast() }
    }
    /// View this [`ArrayCell`] as a [`Cell`] of an [array] of `N` elements.
    pub fn as_std_mut(&mut self) -> &mut Cell<[T; N]> {
        unsafe { &mut *(self as *mut Self).cast() }
    }
    /// View this [`ArrayCell`] as an [array] of `N` [`Cell`]s.
    pub fn as_std_transposed_mut(&mut self) -> &mut [Cell<T>; N] {
        unsafe { &mut *(self as *mut Self).cast() }
    }
    /// View a [`Cell`] of an [array] of `N` elements as an [`ArrayCell`].
    pub fn from_std_mut(std: &mut Cell<[T; N]>) -> &mut Self {
        unsafe { &mut *(std as *mut Cell<[T; N]>).cast() }
    }
    /// View an [array] of `N` [`Cell`]s as an [`ArrayCell`].
    pub fn from_std_transposed_mut(std: &mut [Cell<T>; N]) -> &mut Self {
        unsafe { &mut *(std as *mut [Cell<T>; N]).cast() }
    }
}

#[cfg(all(feature = "assume_cell_layout", feature = "alloc"))]
impl<T, const N: usize> ArrayCell<T, N> {
    /// View this [`ArrayCell`] as a [`Cell`] of an [array] of `N` elements.
    pub fn into_std_boxed(self: Box<Self>) -> Box<Cell<[T; N]>> {
        unsafe { Box::from_raw(Box::into_raw(self).cast()) }
    }
    /// View this [`ArrayCell`] as an [array] of `N` [`Cell`]s.
    pub fn into_std_transposed_boxed(self: Box<Self>) -> Box<[Cell<T>; N]> {
        unsafe { Box::from_raw(Box::into_raw(self).cast()) }
    }
    /// View a [`Cell`] of an [array] of `N` elements as an [`ArrayCell`].
    pub fn from_std_boxed(std: Box<Cell<[T; N]>>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(std).cast()) }
    }
    /// View an [array] of `N` [`Cell`]s as an [`ArrayCell`].
    pub fn from_std_transposed_boxed(std: Box<[Cell<T>; N]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(std).cast()) }
    }
}

#[cfg(all(feature = "assume_cell_layout", feature = "rc"))]
impl<T, const N: usize> ArrayCell<T, N> {
    /// View this [`ArrayCell`] as a [`Cell`] of an [array] of `N` elements.
    pub fn into_std_rc(self: Rc<Self>) -> Rc<Cell<[T; N]>> {
        unsafe { Rc::from_raw(Rc::into_raw(self).cast()) }
    }
    /// View this [`ArrayCell`] as an [array] of `N` [`Cell`]s.
    pub fn into_std_transposed_rc(self: Rc<Self>) -> Rc<[Cell<T>; N]> {
        unsafe { Rc::from_raw(Rc::into_raw(self).cast()) }
    }
    /// View a [`Cell`] of an [array] of `N` elements as an [`ArrayCell`].
    pub fn from_std_rc(std: Rc<Cell<[T; N]>>) -> Rc<Self> {
        unsafe { Rc::from_raw(Rc::into_raw(std).cast()) }
    }
    /// View an [array] of `N` [`Cell`]s as an [`ArrayCell`].
    pub fn from_std_transposed_rc(std: Rc<[Cell<T>; N]>) -> Rc<Self> {
        unsafe { Rc::from_raw(Rc::into_raw(std).cast()) }
    }
}

impl<T, const N: usize> ArrayCell<T, N> {
    pub(crate) fn as_raw_ref(&self) -> &[UnsafeCell<T>; N] {
        unsafe { &*(self as *const Self).cast() }
    }
    pub(crate) fn as_raw_mut(&mut self) -> &mut [UnsafeCell<T>; N] {
        unsafe { &mut *(self as *mut Self).cast() }
    }
    pub(crate) fn from_raw_ref(this: &[UnsafeCell<T>; N]) -> &Self {
        unsafe { &*(this as *const [UnsafeCell<T>; N]).cast() }
    }
    pub(crate) fn from_raw_mut(this: &mut [UnsafeCell<T>; N]) -> &mut Self {
        unsafe { &mut *(this as *mut [UnsafeCell<T>; N]).cast() }
    }
    #[cfg(feature = "alloc")]
    pub(crate) fn into_raw_boxed(self: Box<Self>) -> Box<[UnsafeCell<T>; N]> {
        unsafe { Box::from_raw(Box::into_raw(self).cast()) }
    }
    #[cfg(feature = "alloc")]
    pub(crate) fn from_raw_boxed(this: Box<[UnsafeCell<T>; N]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(this).cast()) }
    }
    #[cfg(feature = "rc")]
    pub(crate) fn into_raw_rc(self: Rc<Self>) -> Rc<[UnsafeCell<T>; N]> {
        unsafe { Rc::from_raw(Rc::into_raw(self).cast()) }
    }
    #[cfg(feature = "rc")]
    pub(crate) fn from_raw_rc(this: Rc<[UnsafeCell<T>; N]>) -> Rc<Self> {
        unsafe { Rc::from_raw(Rc::into_raw(this).cast()) }
    }

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

    /// Wraps a [boxed](alloc::boxed::Box) [array] in an [`ArrayCell`].
    #[cfg(feature = "alloc")]
    pub fn new_boxed(inner: Box<[T; N]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(inner) as *mut _) }
    }

    /// Wraps a [reference-counted](alloc::rc::Rc) [array] in an `ArrayCell`, if it is uniquely owned.
    #[cfg(feature = "rc")]
    pub fn try_new_rc(mut inner: Rc<[T; N]>) -> Result<Rc<Self>, Rc<[T; N]>> {
        match Rc::get_mut(&mut inner) {
            Some(_unique) => Ok(unsafe { Rc::from_raw(Rc::into_raw(inner).cast()) }),
            None => Err(inner),
        }
    }

    /// Unwraps a [reference-counted](alloc::rc::Rc) [`ArrayCell`] into an [array], if it is uniquely owned.
    #[cfg(feature = "rc")]
    pub fn try_into_inner_rc(mut self: Rc<Self>) -> Result<Rc<[T; N]>, Rc<Self>> {
        match Rc::get_mut(&mut self) {
            Some(_unique) => Ok(unsafe { Rc::from_raw(Rc::into_raw(self).cast()) }),
            None => Err(self),
        }
    }

    #[cfg(feature = "rc")]
    /// Replacement for `From` impl, since `Rc` is not fundamental
    pub fn unsize_rc(self: Rc<Self>) -> Rc<SliceCell<T>> {
        SliceCell::from_raw_rc(self.into_raw_rc())
    }

    /// Unwraps a uniquely borrowed [`ArrayCell`] into an array.
    pub fn get_mut(&mut self) -> &mut [T; N] {
        self.inner.get_mut()
    }

    /// Wraps a uniquely borrowed array in an [`ArrayCell`].
    pub fn from_mut(inner: &mut [T; N]) -> &mut Self {
        unsafe { &mut *(inner as *mut [T; N]).cast() }
    }

    /// Returns the length of the [`ArrayCell`].
    pub const fn len(&self) -> usize {
        N
    }
}

impl<T, const N: usize> AsRef<SliceCell<T>> for ArrayCell<T, N> {
    fn as_ref(&self) -> &SliceCell<T> {
        SliceCell::from_raw_ref(self.as_raw_ref())
    }
}

impl<T, const N: usize> AsMut<SliceCell<T>> for ArrayCell<T, N> {
    fn as_mut(&mut self) -> &mut SliceCell<T> {
        SliceCell::from_raw_mut(self.as_raw_mut())
    }
}

impl<T> AsRef<SliceCell<T>> for SliceCell<T> {
    fn as_ref(&self) -> &SliceCell<T> {
        SliceCell::from_raw_ref(self.as_raw_ref())
    }
}

impl<T> AsMut<SliceCell<T>> for SliceCell<T> {
    fn as_mut(&mut self) -> &mut SliceCell<T> {
        SliceCell::from_raw_mut(self.as_raw_mut())
    }
}

impl<T, const N: usize> Deref for ArrayCell<T, N> {
    type Target = SliceCell<T>;

    fn deref(&self) -> &Self::Target {
        SliceCell::from_raw_ref(self.as_raw_ref())
    }
}

impl<T, const N: usize> DerefMut for ArrayCell<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        SliceCell::from_raw_mut(self.as_raw_mut())
    }
}

#[cfg(feature = "assume_cell_layout")]
impl<T> SliceCell<T> {
    /// View this [`SliceCell`] as a [`Cell`] of a [slice].
    pub fn as_std_ref(&self) -> &Cell<[T]> {
        unsafe { &*(self as *const Self as *const _) }
    }
    /// View this [`SliceCell`] as a [slice] of [`Cell`]s.
    pub fn as_std_transposed_ref(&self) -> &[Cell<T>] {
        unsafe { &*(self as *const Self as *const _) }
    }
    /// View a [`Cell`] of a [slice] as a [`SliceCell`].
    pub fn from_std_ref(std: &Cell<[T]>) -> &Self {
        unsafe { &*(std as *const Cell<[T]> as *const _) }
    }
    /// View a [slice] [`Cell`]s as a [`SliceCell`].
    pub fn from_std_transposed_ref(std: &[Cell<T>]) -> &Self {
        unsafe { &*(std as *const [Cell<T>] as *const _) }
    }
    /// View this [`SliceCell`] as a [`Cell`] of a [slice].
    pub fn as_std_mut(&mut self) -> &mut Cell<[T]> {
        unsafe { &mut *(self as *mut Self as *mut _) }
    }
    /// View this [`SliceCell`] as a [slice] of [`Cell`]s.
    pub fn as_std_transposed_mut(&mut self) -> &mut [Cell<T>] {
        unsafe { &mut *(self as *mut Self as *mut _) }
    }
    /// View a [`Cell`] of a [slice] as a [`SliceCell`].
    pub fn from_std_mut(std: &mut Cell<[T]>) -> &mut Self {
        unsafe { &mut *(std as *mut Cell<[T]> as *mut _) }
    }
    pub fn from_std_transposed_mut(std: &mut [Cell<T>]) -> &mut Self {
        unsafe { &mut *(std as *mut [Cell<T>] as *mut _) }
    }
}

#[cfg(all(feature = "assume_cell_layout", feature = "alloc"))]
impl<T> SliceCell<T> {
    /// View this [`SliceCell`] as a [`Cell`] of a [slice].
    pub fn into_std_boxed(self: Box<Self>) -> Box<Cell<[T]>> {
        unsafe { Box::from_raw(Box::into_raw(self) as *mut _) }
    }
    /// View this [`SliceCell`] as a [slice] of [`Cell`]s.
    pub fn into_std_transposed_boxed(self: Box<Self>) -> Box<[Cell<T>]> {
        unsafe { Box::from_raw(Box::into_raw(self) as *mut _) }
    }
    /// View a [`Cell`] of a [slice] as a [`SliceCell`].
    pub fn from_std_boxed(std: Box<Cell<[T]>>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(std) as *mut _) }
    }
    pub fn from_std_transposed_boxed(std: Box<[Cell<T>]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(std) as *mut _) }
    }
}

#[cfg(all(feature = "assume_cell_layout", feature = "rc"))]
impl<T> SliceCell<T> {
    /// View this [`SliceCell`] as a [`Cell`] of a [slice].
    pub fn into_std_rc(self: Rc<Self>) -> Rc<Cell<[T]>> {
        unsafe { Rc::from_raw(Rc::into_raw(self) as *const _) }
    }
    /// View this [`SliceCell`] as a [slice] of [`Cell`]s.
    pub fn into_std_transposed_rc(self: Rc<Self>) -> Rc<[Cell<T>]> {
        unsafe { Rc::from_raw(Rc::into_raw(self) as *const _) }
    }
    /// View a [`Cell`] of a [slice] as a [`SliceCell`].
    pub fn from_std_rc(std: Rc<Cell<[T]>>) -> Rc<Self> {
        unsafe { Rc::from_raw(Rc::into_raw(std) as *const _) }
    }
    pub fn from_std_transposed_rc(std: Rc<[Cell<T>]>) -> Rc<Self> {
        unsafe { Rc::from_raw(Rc::into_raw(std) as *const _) }
    }
}

impl<T> SliceCell<T> {
    pub(crate) fn as_raw_ref(&self) -> &[UnsafeCell<T>] {
        unsafe { &*(self as *const Self as *const _) }
    }
    pub(crate) fn from_raw_ref(this: &[UnsafeCell<T>]) -> &Self {
        unsafe { &*(this as *const _ as *const _) }
    }
    pub(crate) fn as_raw_mut(&mut self) -> &mut [UnsafeCell<T>] {
        unsafe { &mut *(self as *mut Self as *mut _) }
    }
    pub(crate) fn from_raw_mut(this: &mut [UnsafeCell<T>]) -> &mut Self {
        unsafe { &mut *(this as *mut _ as *mut _) }
    }
    #[cfg(feature = "alloc")]
    pub(crate) fn into_raw_boxed(self: Box<Self>) -> Box<[UnsafeCell<T>]> {
        unsafe { Box::from_raw(Box::into_raw(self) as *mut _) }
    }
    #[cfg(feature = "alloc")]
    pub(crate) fn from_raw_boxed(this: Box<[UnsafeCell<T>]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(this) as *mut _) }
    }
    #[cfg(feature = "rc")]
    pub(crate) fn into_raw_rc(self: Rc<Self>) -> Rc<[UnsafeCell<T>]> {
        unsafe { Rc::from_raw(Rc::into_raw(self) as *mut _) }
    }
    #[cfg(feature = "rc")]
    pub(crate) fn from_raw_rc(this: Rc<[UnsafeCell<T>]>) -> Rc<Self> {
        unsafe { Rc::from_raw(Rc::into_raw(this) as *mut _) }
    }

    /// Returns a raw pointer to the underlying data in this `SliceCell`.
    pub fn as_ptr(&self) -> *mut [T] {
        UnsafeCell::raw_get(&self.inner)
    }

    /// Unwraps a [boxed](alloc::boxed::Box) [`SliceCell`] into a slice.
    #[cfg(feature = "alloc")]
    pub fn into_inner_boxed(self: Box<Self>) -> Box<[T]> {
        unsafe { Box::from_raw(Box::into_raw(self) as *mut _) }
    }

    /// Wraps a [boxed](alloc::boxed::Box) [slice] in a [`SliceCell`].
    #[cfg(feature = "alloc")]
    pub fn new_boxed(inner: Box<[T]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(inner) as *mut _) }
    }

    /// Wraps a [reference-counted](alloc::rc::Rc) [slice] in a `SliceCell`, if it is uniquely owned.
    #[cfg(feature = "rc")]
    pub fn try_new_rc(mut inner: Rc<[T]>) -> Result<Rc<Self>, Rc<[T]>> {
        match Rc::get_mut(&mut inner) {
            Some(_unique) => Ok(unsafe { Rc::from_raw(Rc::into_raw(inner) as *const _) }),
            None => Err(inner),
        }
    }

    /// Unwraps a [reference-counted](alloc::rc::Rc) [`SliceCell`] into an [slice], if it is uniquely owned.
    #[cfg(feature = "rc")]
    pub fn try_into_inner_rc(mut self: Rc<Self>) -> Result<Rc<[T]>, Rc<Self>> {
        match Rc::get_mut(&mut self) {
            Some(_unique) => Ok(unsafe { Rc::from_raw(Rc::into_raw(self) as *const _) }),
            None => Err(self),
        }
    }

    /// Unwraps a uniquely borrowed [`SliceCell`] into a slice.
    pub fn get_mut(&mut self) -> &mut [T] {
        self.inner.get_mut()
    }

    /// Wraps a uniquely borrowed slice in a [`SliceCell`].
    pub fn from_mut(inner: &mut [T]) -> &mut Self {
        unsafe { &mut *(inner as *mut [T] as *mut _) }
    }

    /// Returns the length of the [`SliceCell`].
    pub const fn len(&self) -> usize {
        unsafe { &*(self as *const Self as *const [UnsafeCell<T>]) }.len()
    }

    /// Divide one `SliceCell` into two at an index.
    ///
    /// Panics if `mid > self.len()`.
    ///
    /// See [slice::split_at]
    pub fn split_at(&self, mid: usize) -> (&SliceCell<T>, &SliceCell<T>) {
        let (start, end) = self.as_raw_ref().split_at(mid);
        (Self::from_raw_ref(start), Self::from_raw_ref(end))
    }

    /// Divide one mutable `SliceCell` into two at an index.
    ///
    /// Panics if `mid > self.len()`.
    ///
    /// See [slice::split_at_mut]
    pub fn split_at_mut(&mut self, mid: usize) -> (&mut SliceCell<T>, &mut SliceCell<T>) {
        let (start, end) = self.as_raw_mut().split_at_mut(mid);
        (Self::from_raw_mut(start), Self::from_raw_mut(end))
    }

    /// Returns the first and all the rest of the elements of the `SliceCell`, or None if it is empty.
    ///
    /// See [slice::split_first]
    #[cfg(feature = "assume_cell_layout")]
    pub fn split_first(&self) -> Option<(&Cell<T>, &SliceCell<T>)> {
        let (first, end) = self.as_raw_ref().split_first()?;
        Some((
            unsafe { &*(first as *const UnsafeCell<T> as *const Cell<T>) },
            Self::from_raw_ref(end),
        ))
    }

    /// Returns the first and all the rest of the elements of the `SliceCell`, or None if it is empty.
    ///
    /// See [slice::split_first_mut]
    #[cfg(feature = "assume_cell_layout")]
    pub fn split_first_mut(&mut self) -> Option<(&mut Cell<T>, &mut SliceCell<T>)> {
        let (first, end) = self.as_raw_mut().split_first_mut()?;
        Some((
            unsafe { &mut *(first as *mut UnsafeCell<T> as *mut Cell<T>) },
            Self::from_raw_mut(end),
        ))
    }

    /// Returns the last and all the rest of the elements of the `SliceCell`, or None if it is empty.
    ///
    /// See [slice::split_last]
    #[cfg(feature = "assume_cell_layout")]
    pub fn split_last(&self) -> Option<(&Cell<T>, &SliceCell<T>)> {
        let (last, end) = self.as_raw_ref().split_last()?;
        Some((
            unsafe { &*(last as *const UnsafeCell<T> as *const Cell<T>) },
            Self::from_raw_ref(end),
        ))
    }

    /// Returns the last and all the rest of the elements of the `SliceCell`, or None if it is empty.
    ///
    /// See [slice::split_last_mut]
    #[cfg(feature = "assume_cell_layout")]
    pub fn split_last_mut(&mut self) -> Option<(&mut Cell<T>, &mut SliceCell<T>)> {
        let (last, end) = self.as_raw_mut().split_last_mut()?;
        Some((
            unsafe { &mut *(last as *mut UnsafeCell<T> as *mut Cell<T>) },
            Self::from_raw_mut(end),
        ))
    }

    /// Copies all elements from src into self, using a memcpy.
    ///
    /// The length of src must be the same as self.
    ///
    /// See [slice::copy_from_slice].
    pub fn copy_from_slice(&self, src: &[T])
    where
        T: Copy,
    {
        assert_eq!(self.len(), src.len());
        unsafe { &mut *self.as_ptr() }.copy_from_slice(src);
    }

    /// Clones all elements from src into self.
    ///
    /// The length of src must be the same as self.
    ///
    /// See [slice::copy_from_slice].
    #[cfg(feature = "assume_cell_layout")]
    pub fn clone_from_slice(&self, src: &[T])
    where
        T: Clone,
    {
        assert_eq!(self.len(), src.len());
        // Clone::clone is arbitrary user code, so we can't use `self.inner.get().clone_from_slice()`
        for (dst, val) in self.iter().zip(src.iter().cloned()) {
            dst.set(val);
        }
    }

    /// Take all elements from this `SliceCell` into a mutable slice, leaving `T::default()` in each cell
    #[cfg(feature = "assume_cell_layout")]
    pub fn take_into_slice(&self, dst: &mut [T])
    where
        T: Default,
    {
        assert_eq!(self.len(), dst.len());
        for ((src, dst), val) in self
            .iter()
            .zip(dst.iter_mut())
            .zip(core::iter::repeat_with(T::default))
        {
            let val = src.replace(val);
            *dst = val;
        }
    }

    /// Take all elements from this `SliceCell` into a newly allocated `Vec<T>`, leaving `T::default()` in each cell.
    #[cfg(all(feature = "assume_cell_layout", feature = "alloc"))]
    pub fn take_into_vec(&self) -> Vec<T>
    where
        T: Default,
    {
        self.iter()
            .zip(core::iter::repeat_with(T::default))
            .map(|(src, val)| src.replace(val))
            .collect()
    }

    /// Copy all elements from this `SliceCell` into a mutable slice.
    pub fn copy_into_slice(&self, dst: &mut [T])
    where
        T: Copy,
    {
        assert_eq!(self.len(), dst.len());
        dst.copy_from_slice(unsafe { &*self.inner.get() });
    }

    /// Copy all elements from this `SliceCell` into a newly allocated `Vec<T>`.
    #[cfg(feature = "alloc")]
    pub fn copy_into_vec(&self) -> Vec<T>
    where
        T: Copy,
    {
        let mut vec = Vec::with_capacity(self.len());
        unsafe {
            let dst = &mut vec.spare_capacity_mut()[..self.len()];
            core::ptr::copy_nonoverlapping(
                self.as_ptr() as *const T,
                dst.as_mut_ptr().cast(),
                self.len(),
            );
            vec.set_len(self.len());
        }
        vec
    }

    #[cfg(feature = "alloc")]
    pub fn replace_with_vec(&self, mut src: Vec<T>) {
        self.swap_with_slice(&mut src);
    }

    pub fn swap_with_slice(&self, val: &mut [T]) {
        assert_eq!(self.len(), val.len());
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
        unsafe {
            core::ptr::swap(
                self[a..].inner.get().cast::<T>(),
                self[b..].inner.get().cast::<T>(),
            );
        }
    }

    /// See [`<[T]>::rotate_left`](slice::rotate_left)
    pub fn rotate_left(&self, mid: usize) {
        unsafe { &mut *self.inner.get() }.rotate_left(mid)
    }

    /// See [`<[T]>::rotate_right`](slice::rotate_right)
    pub fn rotate_right(&self, mid: usize) {
        unsafe { &mut *self.inner.get() }.rotate_right(mid)
    }

    /// Fills self with elements by cloning value.
    ///
    /// See also: [`<[T]>::fill`](slice::fill).
    #[cfg(feature = "assume_cell_layout")]
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
    #[cfg(feature = "assume_cell_layout")]
    pub fn fill_with<F>(&self, mut f: F)
    where
        F: FnMut() -> T,
    {
        for dst in self {
            dst.set(f());
        }
    }

    #[cfg(feature = "rc")]
    /// Replacement for `TryFrom` impl, since `Rc` is not fundamental
    pub fn try_size_rc<const N: usize>(self: Rc<Self>) -> Result<Rc<ArrayCell<T, N>>, Rc<Self>> {
        if self.len() == N {
            Ok(ArrayCell::from_raw_rc(
                self.into_raw_rc()
                    .try_into()
                    .expect("already checked the length"),
            ))
        } else {
            Err(self)
        }
    }

    /// N should not be 0.
    ///
    /// Splits the slice into a slice of N-element arrays, starting at the beginning of the slice, and a remainder slice with length strictly less than N.
    pub fn as_chunks<const N: usize>(&self) -> (&SliceCell<[T; N]>, &Self) {
        if N == 0 {
            (SliceCell::from_raw_ref(&[]), self)
        } else {
            let chunk_count = self.len() / N;
            let remainder = self.len() % N;
            let (chunks, remainder) = self.split_at(self.len() - remainder);
            let chunks: &[UnsafeCell<T>] = chunks.as_raw_ref();
            let chunks: &[UnsafeCell<[T; N]>] =
                unsafe { core::slice::from_raw_parts(chunks.as_ptr().cast(), chunk_count) };
            let chunks: &SliceCell<[T; N]> = SliceCell::from_raw_ref(chunks);
            (chunks, remainder)
        }
    }

    /// N should not be 0.
    ///
    /// Splits the slice into a slice of N-element arrays, starting at the end of the slice, and a remainder slice with length strictly less than N.
    pub fn as_rchunks<const N: usize>(&self) -> (&Self, &SliceCell<[T; N]>) {
        if N == 0 {
            (self, SliceCell::from_raw_ref(&[]))
        } else {
            let chunk_count = self.len() / N;
            let remainder = self.len() % N;
            let (remainder, chunks) = self.split_at(remainder);
            let chunks: &[UnsafeCell<T>] = chunks.as_raw_ref();
            let chunks: &[UnsafeCell<[T; N]>] =
                unsafe { core::slice::from_raw_parts(chunks.as_ptr().cast(), chunk_count) };
            let chunks: &SliceCell<[T; N]> = SliceCell::from_raw_ref(chunks);
            (remainder, chunks)
        }
    }

    /// N should not be 0.
    ///
    /// Splits the slice into a slice of N-element arrays, starting at the beginning of the slice, and a remainder slice with length strictly less than N.
    pub fn as_chunks_mut<const N: usize>(&mut self) -> (&mut SliceCell<[T; N]>, &mut Self) {
        if N == 0 {
            (SliceCell::from_raw_mut(&mut []), self)
        } else {
            let chunk_count = self.len() / N;
            let remainder = self.len() % N;
            let (chunks, remainder) = self.split_at_mut(self.len() - remainder);
            let chunks: &mut [UnsafeCell<T>] = chunks.as_raw_mut();
            let chunks: &mut [UnsafeCell<[T; N]>] =
                unsafe { core::slice::from_raw_parts_mut(chunks.as_mut_ptr().cast(), chunk_count) };
            let chunks: &mut SliceCell<[T; N]> = SliceCell::from_raw_mut(chunks);
            (chunks, remainder)
        }
    }

    /// N should not be 0.
    ///
    /// Splits the slice into a slice of N-element arrays, starting at the end of the slice, and a remainder slice with length strictly less than N.
    pub fn as_rchunks_mut<const N: usize>(&mut self) -> (&mut Self, &mut SliceCell<[T; N]>) {
        if N == 0 {
            (self, SliceCell::from_raw_mut(&mut []))
        } else {
            let chunk_count = self.len() / N;
            let remainder = self.len() % N;
            let (remainder, chunks) = self.split_at_mut(remainder);
            let chunks: &mut [UnsafeCell<T>] = chunks.as_raw_mut();
            let chunks: &mut [UnsafeCell<[T; N]>] =
                unsafe { core::slice::from_raw_parts_mut(chunks.as_mut_ptr().cast(), chunk_count) };
            let chunks: &mut SliceCell<[T; N]> = SliceCell::from_raw_mut(chunks);
            (remainder, chunks)
        }
    }

    #[cfg(feature = "assume_cell_layout")]
    pub fn iter(&self) -> core::slice::Iter<'_, Cell<T>> {
        IntoIterator::into_iter(self)
    }

    pub fn iter_mut(&mut self) -> core::slice::IterMut<'_, T> {
        self.get_mut().iter_mut()
    }
}

impl<T, const N: usize> SliceCell<[T; N]> {
    pub fn flatten(&self) -> &SliceCell<T> {
        let new_len = self.len().checked_mul(N).expect("size overflow");
        let this: &[UnsafeCell<[T; N]>] = self.as_raw_ref();
        let this: &[UnsafeCell<T>] =
            unsafe { core::slice::from_raw_parts(this.as_ptr().cast(), new_len) };
        let this: &SliceCell<T> = SliceCell::from_raw_ref(this);
        this
    }
    pub fn flatten_mut(&mut self) -> &mut SliceCell<T> {
        let new_len = self.len().checked_mul(N).expect("size overflow");
        let this: &mut [UnsafeCell<[T; N]>] = self.as_raw_mut();
        let this: &mut [UnsafeCell<T>] =
            unsafe { core::slice::from_raw_parts_mut(this.as_mut_ptr().cast(), new_len) };
        let this: &mut SliceCell<T> = SliceCell::from_raw_mut(this);
        this
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

impl<'a, T, const N: usize> From<&'a ArrayCell<T, N>> for &'a SliceCell<T> {
    fn from(value: &'a ArrayCell<T, N>) -> Self {
        SliceCell::from_raw_ref(value.as_raw_ref())
    }
}

impl<'a, T, const N: usize> From<&'a mut ArrayCell<T, N>> for &'a mut SliceCell<T> {
    fn from(value: &'a mut ArrayCell<T, N>) -> Self {
        SliceCell::from_raw_mut(value.as_raw_mut())
    }
}

#[cfg(feature = "alloc")]
impl<'a, T, const N: usize> From<Box<ArrayCell<T, N>>> for Box<SliceCell<T>> {
    fn from(value: Box<ArrayCell<T, N>>) -> Self {
        SliceCell::from_raw_boxed(value.into_raw_boxed())
    }
}

impl<'a, T, const N: usize> TryFrom<&'a SliceCell<T>> for &'a ArrayCell<T, N> {
    type Error = &'a SliceCell<T>;

    fn try_from(value: &'a SliceCell<T>) -> Result<Self, Self::Error> {
        if value.len() == N {
            Ok(ArrayCell::from_raw_ref(
                value
                    .as_raw_ref()
                    .try_into()
                    .expect("already checked the length"),
            ))
        } else {
            Err(value)
        }
    }
}

impl<'a, T, const N: usize> TryFrom<&'a mut SliceCell<T>> for &'a mut ArrayCell<T, N> {
    type Error = &'a mut SliceCell<T>;

    fn try_from(value: &'a mut SliceCell<T>) -> Result<Self, Self::Error> {
        if value.len() == N {
            Ok(ArrayCell::from_raw_mut(
                value
                    .as_raw_mut()
                    .try_into()
                    .expect("already checked the length"),
            ))
        } else {
            Err(value)
        }
    }
}

#[cfg(feature = "alloc")]
impl<'a, T, const N: usize> TryFrom<Box<SliceCell<T>>> for Box<ArrayCell<T, N>> {
    type Error = Box<SliceCell<T>>;

    fn try_from(value: Box<SliceCell<T>>) -> Result<Self, Self::Error> {
        if value.len() == N {
            Ok(ArrayCell::from_raw_boxed(
                value
                    .into_raw_boxed()
                    .try_into()
                    .expect("already checked the length"),
            ))
        } else {
            Err(value)
        }
    }
}

#[cfg(feature = "assume_cell_layout")]
impl<'a, T> IntoIterator for &'a SliceCell<T> {
    type Item = &'a Cell<T>;

    type IntoIter = core::slice::Iter<'a, Cell<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_std_transposed_ref().iter()
    }
}

#[cfg(feature = "assume_cell_layout")]
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
        self.get_mut().iter_mut()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut ArrayCell<T, N> {
    type Item = &'a mut T;

    type IntoIter = core::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.get_mut().iter_mut()
    }
}
