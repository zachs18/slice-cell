#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "alloc")]
use alloc::boxed::Box;
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
    pub fn as_std(&self) -> &Cell<[T; N]> {
        unsafe { &*(self as *const Self).cast() }
    }
    pub fn as_std_transposed(&self) -> &[Cell<T>; N] {
        unsafe { &*(self as *const Self).cast() }
    }
    pub fn from_std(std: &Cell<[T; N]>) -> &Self {
        unsafe { &*(std as *const Cell<[T; N]>).cast() }
    }
    pub fn from_std_transposed(std: &[Cell<T>; N]) -> &Self {
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
    pub fn as_std(&self) -> &Cell<[T]> {
        unsafe { &*(self as *const Self as *const _) }
    }
    pub fn as_std_transposed(&self) -> &[Cell<T>] {
        unsafe { &*(self as *const Self as *const _) }
    }
    pub fn from_std(std: &Cell<[T]>) -> &Self {
        unsafe { &*(std as *const Cell<[T]> as *const _) }
    }
    pub fn from_std_transposed(std: &[Cell<T>]) -> &Self {
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
}

#[cfg(feature = "assume_cell_layout")]
impl<T, I: SliceCellIndex<Self>> Index<I> for SliceCell<T> {
    type Output = <I as SliceCellIndex<Self>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        index.get(self).unwrap()
    }
}
