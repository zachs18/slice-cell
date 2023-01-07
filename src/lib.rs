#![no_std]

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
use core::ops::Deref;
use core::ops::DerefMut;
use core::ops::Index;
use index::SliceCellIndex;

mod index;
#[cfg(feature = "std")]
pub mod io;

#[repr(transparent)]
pub struct ArrayCell<T, const N: usize> {
    inner: UnsafeCell<[T; N]>,
}
#[repr(transparent)]
pub struct SliceCell<T> {
    inner: UnsafeCell<[T]>,
}

#[cfg(feature = "assume_cell_layout")]
impl<T, const N: usize> ArrayCell<T, N> {
    pub fn as_std_ref(&self) -> &Cell<[T; N]> {
        unsafe { &*(self as *const Self).cast() }
    }
    pub fn as_std_transposed_ref(&self) -> &[Cell<T>; N] {
        unsafe { &*(self as *const Self).cast() }
    }
    pub fn from_std_ref(std: &Cell<[T; N]>) -> &Self {
        unsafe { &*(std as *const Cell<[T; N]>).cast() }
    }
    pub fn from_std_transposed_ref(std: &[Cell<T>; N]) -> &Self {
        unsafe { &*(std as *const [Cell<T>; N]).cast() }
    }
    pub fn as_std_mut(&mut self) -> &mut Cell<[T; N]> {
        unsafe { &mut *(self as *mut Self).cast() }
    }
    pub fn as_std_transposed_mut(&mut self) -> &mut [Cell<T>; N] {
        unsafe { &mut *(self as *mut Self).cast() }
    }
    pub fn from_std_mut(std: &mut Cell<[T; N]>) -> &mut Self {
        unsafe { &mut *(std as *mut Cell<[T; N]>).cast() }
    }
    pub fn from_std_transposed_mut(std: &mut [Cell<T>; N]) -> &mut Self {
        unsafe { &mut *(std as *mut [Cell<T>; N]).cast() }
    }
}

#[cfg(all(feature = "assume_cell_layout", feature = "alloc"))]
impl<T, const N: usize> ArrayCell<T, N> {
    pub fn into_std_boxed(self: Box<Self>) -> Box<Cell<[T; N]>> {
        unsafe { Box::from_raw(Box::into_raw(self).cast()) }
    }
    pub fn into_std_transposed_boxed(self: Box<Self>) -> Box<[Cell<T>; N]> {
        unsafe { Box::from_raw(Box::into_raw(self).cast()) }
    }
    pub fn from_std_boxed(std: Box<Cell<[T; N]>>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(std).cast()) }
    }
    pub fn from_std_transposed_boxed(std: Box<[Cell<T>; N]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(std).cast()) }
    }
}

#[cfg(all(feature = "assume_cell_layout", feature = "rc"))]
impl<T, const N: usize> ArrayCell<T, N> {
    pub fn into_std_rc(self: Rc<Self>) -> Rc<Cell<[T; N]>> {
        unsafe { Rc::from_raw(Rc::into_raw(self).cast()) }
    }
    pub fn into_std_transposed_rc(self: Rc<Self>) -> Rc<[Cell<T>; N]> {
        unsafe { Rc::from_raw(Rc::into_raw(self).cast()) }
    }
    pub fn from_std_rc(std: Rc<Cell<[T; N]>>) -> Rc<Self> {
        unsafe { Rc::from_raw(Rc::into_raw(std).cast()) }
    }
    pub fn from_std_transposed_rc(std: Rc<[Cell<T>; N]>) -> Rc<Self> {
        unsafe { Rc::from_raw(Rc::into_raw(std).cast()) }
    }
}

impl<T, const N: usize> ArrayCell<T, N> {
    pub(crate) fn as_raw(&self) -> &[UnsafeCell<T>; N] {
        unsafe { &*(self as *const Self).cast() }
    }
    pub(crate) fn as_raw_mut(&mut self) -> &mut [UnsafeCell<T>; N] {
        unsafe { &mut *(self as *mut Self).cast() }
    }

    pub fn into_inner(self) -> [T; N] {
        self.inner.into_inner()
    }

    pub fn new(inner: [T; N]) -> Self {
        Self {
            inner: UnsafeCell::new(inner),
        }
    }

    #[cfg(feature = "alloc")]
    pub fn new_boxed(inner: Box<[T; N]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(inner) as *mut _) }
    }

    #[cfg(feature = "rc")]
    pub fn try_new_rc(mut inner: Rc<[T; N]>) -> Result<Rc<Self>, Rc<[T; N]>> {
        match Rc::get_mut(&mut inner) {
            Some(_unique) => Ok(unsafe { Rc::from_raw(Rc::into_raw(inner).cast()) }),
            None => Err(inner),
        }
    }

    #[cfg(feature = "rc")]
    pub fn try_into_inner_rc(mut self: Rc<Self>) -> Result<Rc<[T; N]>, Rc<Self>> {
        match Rc::get_mut(&mut self) {
            Some(_unique) => Ok(unsafe { Rc::from_raw(Rc::into_raw(self).cast()) }),
            None => Err(self),
        }
    }

    pub fn get_mut(&mut self) -> &mut [T; N] {
        self.inner.get_mut()
    }

    pub fn from_mut(inner: &mut [T; N]) -> &mut Self {
        unsafe { &mut *(inner as *mut [T; N]).cast() }
    }

    pub const fn len(&self) -> usize {
        N
    }
}

impl<T, const N: usize> AsRef<SliceCell<T>> for ArrayCell<T, N> {
    fn as_ref(&self) -> &SliceCell<T> {
        SliceCell::from_raw(self.as_raw())
    }
}

impl<T, const N: usize> AsMut<SliceCell<T>> for ArrayCell<T, N> {
    fn as_mut(&mut self) -> &mut SliceCell<T> {
        SliceCell::from_raw_mut(self.as_raw_mut())
    }
}

impl<T> AsRef<SliceCell<T>> for SliceCell<T> {
    fn as_ref(&self) -> &SliceCell<T> {
        SliceCell::from_raw(self.as_raw())
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
        SliceCell::from_raw(self.as_raw())
    }
}

impl<T, const N: usize> DerefMut for ArrayCell<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        SliceCell::from_raw_mut(self.as_raw_mut())
    }
}

#[cfg(feature = "assume_cell_layout")]
impl<T> SliceCell<T> {
    pub fn as_std_ref(&self) -> &Cell<[T]> {
        unsafe { &*(self as *const Self as *const _) }
    }
    pub fn as_std_transposed_ref(&self) -> &[Cell<T>] {
        unsafe { &*(self as *const Self as *const _) }
    }
    pub fn from_std_ref(std: &Cell<[T]>) -> &Self {
        unsafe { &*(std as *const Cell<[T]> as *const _) }
    }
    pub fn from_std_transposed_ref(std: &[Cell<T>]) -> &Self {
        unsafe { &*(std as *const [Cell<T>] as *const _) }
    }
    pub fn as_std_mut(&mut self) -> &mut Cell<[T]> {
        unsafe { &mut *(self as *mut Self as *mut _) }
    }
    pub fn as_std_transposed_mut(&mut self) -> &mut [Cell<T>] {
        unsafe { &mut *(self as *mut Self as *mut _) }
    }
    pub fn from_std_mut(std: &mut Cell<[T]>) -> &mut Self {
        unsafe { &mut *(std as *mut Cell<[T]> as *mut _) }
    }
    pub fn from_std_transposed_mut(std: &mut [Cell<T>]) -> &mut Self {
        unsafe { &mut *(std as *mut [Cell<T>] as *mut _) }
    }
}

#[cfg(all(feature = "assume_cell_layout", feature = "alloc"))]
impl<T> SliceCell<T> {
    pub fn into_std_boxed(self: Box<Self>) -> Box<Cell<[T]>> {
        unsafe { Box::from_raw(Box::into_raw(self) as *mut _) }
    }
    pub fn into_std_transposed_boxed(self: Box<Self>) -> Box<[Cell<T>]> {
        unsafe { Box::from_raw(Box::into_raw(self) as *mut _) }
    }
    pub fn from_std_boxed(std: Box<Cell<[T]>>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(std) as *mut _) }
    }
    pub fn from_std_transposed_boxed(std: Box<[Cell<T>]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(std) as *mut _) }
    }
}

#[cfg(all(feature = "assume_cell_layout", feature = "rc"))]
impl<T> SliceCell<T> {
    pub fn into_std_rc(self: Rc<Self>) -> Rc<Cell<[T]>> {
        unsafe { Rc::from_raw(Rc::into_raw(self) as *const _) }
    }
    pub fn into_std_transposed_rc(self: Rc<Self>) -> Rc<[Cell<T>]> {
        unsafe { Rc::from_raw(Rc::into_raw(self) as *const _) }
    }
    pub fn from_std_rc(std: Rc<Cell<[T]>>) -> Rc<Self> {
        unsafe { Rc::from_raw(Rc::into_raw(std) as *const _) }
    }
    pub fn from_std_transposed_rc(std: Rc<[Cell<T>]>) -> Rc<Self> {
        unsafe { Rc::from_raw(Rc::into_raw(std) as *const _) }
    }
}

impl<T> SliceCell<T> {
    pub(crate) fn as_raw(&self) -> &[UnsafeCell<T>] {
        unsafe { &*(self as *const Self as *const _) }
    }
    pub(crate) fn as_raw_mut(&mut self) -> &mut [UnsafeCell<T>] {
        unsafe { &mut *(self as *mut Self as *mut _) }
    }
    pub(crate) fn from_raw(this: &[UnsafeCell<T>]) -> &Self {
        unsafe { &*(this as *const _ as *const _) }
    }
    pub(crate) fn from_raw_mut(this: &mut [UnsafeCell<T>]) -> &mut Self {
        unsafe { &mut *(this as *mut _ as *mut _) }
    }

    pub fn as_ptr(&self) -> *mut T {
        UnsafeCell::raw_get(&self.inner).cast()
    }

    #[cfg(feature = "alloc")]
    pub fn into_inner_boxed(self: Box<Self>) -> Box<[T]> {
        unsafe { Box::from_raw(Box::into_raw(self) as *mut _) }
    }

    #[cfg(feature = "alloc")]
    pub fn new_boxed(inner: Box<[T]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(inner) as *mut _) }
    }

    #[cfg(feature = "rc")]
    pub fn try_new_rc(mut inner: Rc<[T]>) -> Result<Rc<Self>, Rc<[T]>> {
        match Rc::get_mut(&mut inner) {
            Some(_unique) => Ok(unsafe { Rc::from_raw(Rc::into_raw(inner) as *const _) }),
            None => Err(inner),
        }
    }

    #[cfg(feature = "rc")]
    pub fn try_into_inner_rc(mut self: Rc<Self>) -> Result<Rc<[T]>, Rc<Self>> {
        match Rc::get_mut(&mut self) {
            Some(_unique) => Ok(unsafe { Rc::from_raw(Rc::into_raw(self) as *const _) }),
            None => Err(self),
        }
    }

    pub fn get(&self) -> *mut [T] {
        UnsafeCell::get(&self.inner)
    }

    pub fn get_mut(&mut self) -> &mut [T] {
        self.inner.get_mut()
    }

    pub fn from_mut(inner: &mut [T]) -> &mut Self {
        unsafe { &mut *(inner as *mut [T] as *mut _) }
    }

    pub const fn len(&self) -> usize {
        unsafe { &*(self as *const Self as *const [UnsafeCell<T>]) }.len()
    }

    pub fn split_at(&self, mid: usize) -> (&SliceCell<T>, &SliceCell<T>) {
        let (start, end) = self.as_raw().split_at(mid);
        (Self::from_raw(start), Self::from_raw(end))
    }

    pub fn split_at_mut(&mut self, mid: usize) -> (&mut SliceCell<T>, &mut SliceCell<T>) {
        let (start, end) = self.as_raw_mut().split_at_mut(mid);
        (Self::from_raw_mut(start), Self::from_raw_mut(end))
    }

    pub fn copy_from_slice(&self, src: &[T])
    where
        T: Copy,
    {
        assert_eq!(self.len(), src.len());
        unsafe { &mut *self.get() }.copy_from_slice(src);
    }

    pub fn clone_from_slice(&self, src: &[T])
    where
        T: Clone,
    {
        assert_eq!(self.len(), src.len());
        // Clone::clone is arbitrary user code, so we can't use `self.get().clone_from_slice()`
        for i in 0..self.len() {
            let val = src[i].clone();
            unsafe {
                *self[i..].as_ptr() = val;
            }
        }
    }

    // pub fn take_into_slice(&self, dst: &mut [T])
    // where
    //     T: Default,
    // {
    //     assert_eq!(self.len(), dst.len());
    //     dst.copy_from_slice(unsafe { &*self.get() });
    // }

    pub fn copy_into_slice(&self, dst: &mut [T])
    where
        T: Copy,
    {
        assert_eq!(self.len(), dst.len());
        dst.copy_from_slice(unsafe { &*self.get() });
    }

    #[cfg(feature = "alloc")]
    pub fn copy_into_vec(&self) -> Vec<T>
    where
        T: Copy,
    {
        let mut vec = Vec::with_capacity(self.len());
        unsafe {
            let dst = &mut vec.spare_capacity_mut()[..self.len()];
            std::ptr::copy_nonoverlapping(self.as_ptr(), dst.as_mut_ptr().cast(), self.len());
            vec.set_len(self.len());
        }
        vec
    }

    #[cfg(feature = "alloc")]
    pub fn replace_with_vec(&self, mut src: Vec<T>) {
        assert_eq!(self.len(), src.len());
        unsafe {
            std::ptr::copy_nonoverlapping(src.as_ptr(), self.as_ptr(), self.len());
            src.set_len(0);
        }
    }

    pub fn swap_with_slice(&self, val: &mut [T]) {
        assert_eq!(self.len(), val.len());
        unsafe { &mut *self.get() }.swap_with_slice(val);
    }

    #[cfg(any())]
    pub fn swap_with_slicecell(&self, other: &Self) -> Result {
        todo!("decide what to do with overlapping slices. Probably just return an error?")
    }

    #[cfg(feature = "rc")]
    /// Replacement for `TryInto` impl, since `Rc` is not fundamental
    pub fn try_cast_rc<const N: usize>(self: Rc<Self>) -> Result<Rc<ArrayCell<T, N>>, Rc<Self>> {
        if self.len() == N {
            Ok(unsafe { Rc::from_raw(Rc::into_raw(self).cast()) })
        } else {
            Err(self)
        }
    }

    /// N should not be 0
    pub fn as_chunks<const N: usize>(&self) -> (&SliceCell<[T; N]>, &Self) {
        if N == 0 {
            (SliceCell::from_raw(&[]), self)
        } else {
            let chunk_count = self.len() / N;
            let remainder = self.len() % N;
            let (chunks, remainder) = self.split_at(self.len() - remainder);
            let chunks: &[UnsafeCell<T>] = chunks.as_raw();
            let chunks: &[UnsafeCell<[T; N]>] =
                unsafe { std::slice::from_raw_parts(chunks.as_ptr().cast(), chunk_count) };
            let chunks: &SliceCell<[T; N]> = SliceCell::from_raw(chunks);
            (chunks, remainder)
        }
    }

    /// N should not be 0
    pub fn as_rchunks<const N: usize>(&self) -> (&Self, &SliceCell<[T; N]>) {
        if N == 0 {
            (self, SliceCell::from_raw(&[]))
        } else {
            let chunk_count = self.len() / N;
            let remainder = self.len() % N;
            let (remainder, chunks) = self.split_at(remainder);
            let chunks: &[UnsafeCell<T>] = chunks.as_raw();
            let chunks: &[UnsafeCell<[T; N]>] =
                unsafe { std::slice::from_raw_parts(chunks.as_ptr().cast(), chunk_count) };
            let chunks: &SliceCell<[T; N]> = SliceCell::from_raw(chunks);
            (remainder, chunks)
        }
    }

    /// N should not be 0
    pub fn as_chunks_mut<const N: usize>(&mut self) -> (&mut SliceCell<[T; N]>, &mut Self) {
        if N == 0 {
            (SliceCell::from_raw_mut(&mut []), self)
        } else {
            let chunk_count = self.len() / N;
            let remainder = self.len() % N;
            let (chunks, remainder) = self.split_at_mut(self.len() - remainder);
            let chunks: &mut [UnsafeCell<T>] = chunks.as_raw_mut();
            let chunks: &mut [UnsafeCell<[T; N]>] =
                unsafe { std::slice::from_raw_parts_mut(chunks.as_mut_ptr().cast(), chunk_count) };
            let chunks: &mut SliceCell<[T; N]> = SliceCell::from_raw_mut(chunks);
            (chunks, remainder)
        }
    }

    /// N should not be 0
    pub fn as_rchunks_mut<const N: usize>(&mut self) -> (&mut Self, &mut SliceCell<[T; N]>) {
        if N == 0 {
            (self, SliceCell::from_raw_mut(&mut []))
        } else {
            let chunk_count = self.len() / N;
            let remainder = self.len() % N;
            let (remainder, chunks) = self.split_at_mut(remainder);
            let chunks: &mut [UnsafeCell<T>] = chunks.as_raw_mut();
            let chunks: &mut [UnsafeCell<[T; N]>] =
                unsafe { std::slice::from_raw_parts_mut(chunks.as_mut_ptr().cast(), chunk_count) };
            let chunks: &mut SliceCell<[T; N]> = SliceCell::from_raw_mut(chunks);
            (remainder, chunks)
        }
    }
}

impl<T, const N: usize> SliceCell<[T; N]> {
    pub fn flatten(&self) -> &SliceCell<T> {
        let new_len = self.len().checked_mul(N).expect("size overflow");
        let this: &[UnsafeCell<[T; N]>] = self.as_raw();
        let this: &[UnsafeCell<T>] =
            unsafe { std::slice::from_raw_parts(this.as_ptr().cast(), new_len) };
        let this: &SliceCell<T> = SliceCell::from_raw(this);
        this
    }
    pub fn flatten_mut(&mut self) -> &mut SliceCell<T> {
        let new_len = self.len().checked_mul(N).expect("size overflow");
        let this: &mut [UnsafeCell<[T; N]>] = self.as_raw_mut();
        let this: &mut [UnsafeCell<T>] =
            unsafe { std::slice::from_raw_parts_mut(this.as_mut_ptr().cast(), new_len) };
        let this: &mut SliceCell<T> = SliceCell::from_raw_mut(this);
        this
    }
}

#[cfg(feature = "assume_cell_layout")]
impl<T, I: SliceCellIndex<Self>> Index<I> for SliceCell<T> {
    type Output = <I as SliceCellIndex<Self>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        index.get(self).unwrap()
    }
}

impl<'a, T, const N: usize> TryFrom<&'a SliceCell<T>> for &'a ArrayCell<T, N> {
    type Error = &'a SliceCell<T>;

    fn try_from(value: &'a SliceCell<T>) -> Result<Self, Self::Error> {
        if value.len() == N {
            Ok(unsafe { &*(value as *const _ as *const Self) })
        } else {
            Err(value)
        }
    }
}

impl<'a, T, const N: usize> TryFrom<&'a mut SliceCell<T>> for &'a mut ArrayCell<T, N> {
    type Error = &'a mut SliceCell<T>;

    fn try_from(value: &'a mut SliceCell<T>) -> Result<Self, Self::Error> {
        if value.len() == N {
            Ok(unsafe { &mut *(value as *mut _ as *mut Self) })
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
            Ok(unsafe { Box::from_raw(Box::into_raw(value).cast()) })
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

#[cfg(feature = "assume_cell_layout")]
impl<'a, T> IntoIterator for &'a mut SliceCell<T> {
    type Item = &'a mut Cell<T>;

    type IntoIter = core::slice::IterMut<'a, Cell<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_std_transposed_mut().iter_mut()
    }
}

#[cfg(feature = "assume_cell_layout")]
impl<'a, T, const N: usize> IntoIterator for &'a mut ArrayCell<T, N> {
    type Item = &'a mut Cell<T>;

    type IntoIter = core::slice::IterMut<'a, Cell<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_std_transposed_mut().iter_mut()
    }
}
