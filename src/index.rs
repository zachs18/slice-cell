#[cfg(feature = "assume_cell_layout")]
use core::cell::Cell;

use crate::{ArrayCell, SliceCell};

pub trait SliceCellIndex<T: ?Sized> {
    type Output: ?Sized;

    fn get(self, slice: &T) -> Option<&Self::Output>;
    fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;
}

#[cfg(feature = "assume_cell_layout")]
impl<T> SliceCellIndex<SliceCell<T>> for usize {
    type Output = Cell<T>;

    fn get(self, slice: &SliceCell<T>) -> Option<&Self::Output> {
        slice.as_std_transposed_ref().get(self)
    }

    fn get_mut(self, slice: &mut SliceCell<T>) -> Option<&mut Self::Output> {
        slice.as_std_transposed_mut().get_mut(self)
    }
}

#[cfg(feature = "assume_cell_layout")]
impl<T, const N: usize> SliceCellIndex<ArrayCell<T, N>> for usize {
    type Output = Cell<T>;

    fn get(self, array: &ArrayCell<T, N>) -> Option<&Self::Output> {
        array.as_std_transposed_ref().get(self)
    }

    fn get_mut(self, array: &mut ArrayCell<T, N>) -> Option<&mut Self::Output> {
        array.as_std_transposed_mut().get_mut(self)
    }
}

macro_rules! delegate_to_slice {
    ($($idx:ty);* $(;)?) => { $(
        impl<T> SliceCellIndex<SliceCell<T>> for $idx {
            type Output = SliceCell<T>;

            fn get(self, slice: &SliceCell<T>) -> Option<&Self::Output> {
                let slice = slice.as_raw_ref().get(self)?;
                // SAFETY: the input to `SliceCell::from_raw_ref` is the result of `SliceCell::into_raw_ref`.
                Some(unsafe {SliceCell::from_raw_ref(slice)})
            }

            fn get_mut(self, slice: &mut SliceCell<T>) -> Option<&mut Self::Output> {
                let slice = slice.as_raw_mut().get_mut(self)?;
                // SAFETY: the input to `SliceCell::from_raw_mut` is the result of `SliceCell::into_raw_mut`.
                Some(unsafe { SliceCell::from_raw_mut(slice)})
            }
        }
        impl<T, const N: usize> SliceCellIndex<ArrayCell<T, N>> for $idx {
            type Output = SliceCell<T>;

            fn get(self, slice: &ArrayCell<T, N>) -> Option<&Self::Output> {
                let slice = slice.as_raw_ref().get(self)?;
                // SAFETY: the input to `SliceCell::from_raw_ref` is the result of `ArrayCell::into_raw_ref`.
                Some(unsafe { SliceCell::from_raw_ref(slice) })
            }

            fn get_mut(self, slice: &mut ArrayCell<T, N>) -> Option<&mut Self::Output> {
                let slice = slice.as_raw_mut().get_mut(self)?;
                // SAFETY: the input to `SliceCell::from_raw_mut` is the result of `ArrayCell::into_raw_mut`.
                Some(unsafe {SliceCell::from_raw_mut(slice)})
            }
        }
    )* };
}

delegate_to_slice! {
    core::ops::RangeFull;
    core::ops::Range<usize>;
    core::ops::RangeInclusive<usize>;
    core::ops::RangeTo<usize>;
    core::ops::RangeFrom<usize>;
    core::ops::RangeToInclusive<usize>;
}
