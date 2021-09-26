/* SPDX-License-Identifier: (Apache-2.0 OR MIT OR Zlib) */
/* Copyright © 2021 Violet Leonard */

//! This crate provides abstractions to type-erase various lists
//! (Vecs and slices).
//!
//! Type erasing a list still requires the contained type to be homogeneous.
//! The [`VecAny`] type provided in this crate is semantically a
//! `Vec<dyn Any>`, where the trait object provides indirection to a single
//! type.  For heterogeneous lists, some indirection is needed, as found
//! in `Vec<Box<dyn Any>>`.

#![no_std]
#![warn(missing_docs)]
#![warn(clippy::pedantic)]

#[cfg(feature = "alloc")]
extern crate alloc;

use core::{
    any::{Any, TypeId},
    marker::PhantomData,
    slice,
};

#[cfg(feature = "alloc")]
mod vec;
#[cfg(feature = "alloc")]
pub use vec::*;

#[derive(Debug)]
struct Metadata {
    type_id: fn() -> TypeId,
    #[cfg(feature = "alloc")]
    drop: unsafe fn(*mut (), usize, usize),
}

impl Metadata {
    fn is_deferred(&'static self) -> bool {
        (self.type_id)() == TypeId::of::<DeferredValue>()
    }
}

trait HasMetadata {
    const META: &'static Metadata;
}

impl<T: Any> HasMetadata for T {
    const META: &'static Metadata = &Metadata {
        type_id: TypeId::of::<Self>,
        #[cfg(feature = "alloc")]
        drop: vec::drop::<Self>,
    };
}

enum DeferredValue {}
enum OpaqueValue {}

/// A type-erased slice.
///
/// Semantically `&[dyn Any]`.
///
/// # Examples
/// ```
/// use list_any::SliceAny;
/// let data: &[u8] = b"hello";
/// let slice_any: SliceAny = SliceAny::from(data);
/// assert_eq!(slice_any.downcast::<u8>(), Some(data));
/// ```
#[derive(Debug)]
pub struct SliceAny<'a, B: ?Sized = dyn Any + Send + Sync> {
    ptr: *const (),
    meta: &'static Metadata,
    len: usize,
    _marker: PhantomData<&'a B>,
}

unsafe impl<'a, B: ?Sized + Send + Sync> Send for SliceAny<'a, B> {}
unsafe impl<'a, B: ?Sized + Sync> Sync for SliceAny<'a, B> {}

impl<'a, B: ?Sized, T: AnyBound<B>> From<&'a [T]> for SliceAny<'a, B> {
    fn from(slice: &[T]) -> Self {
        let ptr = slice.as_ptr().cast();
        let meta = T::META;
        let len = slice.len();
        Self {
            ptr,
            meta,
            len,
            _marker: PhantomData,
        }
    }
}

impl<'a> SliceAny<'a> {
    /// Create a `SliceAny` with a length of 0, for which downcasting will
    /// always return `None`.
    ///
    /// ```
    /// use list_any::SliceAny;
    /// let slice = SliceAny::opaque();
    /// assert_eq!(slice.downcast::<f64>(), None);
    /// assert_eq!(slice.downcast::<u32>(), None);
    /// assert_eq!(slice.downcast::<()>(), None);
    /// ```
    #[must_use]
    pub fn opaque() -> Self {
        let slice: &[OpaqueValue] = &[];
        Self::from(slice)
    }

    /// Create a `SliceAny` with a length of 0, for which downcasting will
    /// always return `Some`.
    ///
    /// ```
    /// use list_any::SliceAny;
    /// let slice = SliceAny::deferred();
    /// assert_eq!(slice.downcast::<f64>(), Some(&[][..]));
    /// assert_eq!(slice.downcast::<u32>(), Some(&[][..]));
    /// assert_eq!(slice.downcast::<()>(), Some(&[][..]));
    /// ```
    #[must_use]
    pub fn deferred() -> Self {
        let slice: &[DeferredValue] = &[];
        Self::from(slice)
    }
}

impl<'a, B: ?Sized> SliceAny<'a, B> {
    /// Returns the number of elements in the slice.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the slice has a length of 0.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the `TypeId` of the elements contained in this slice.
    ///
    /// # Examples
    /// ```
    /// use core::any::TypeId;
    /// use list_any::SliceAny;
    /// let data: &[u8] = b"hello";
    /// let slice_any: SliceAny = SliceAny::from(data);
    /// assert_eq!(slice_any.type_id_of_element(), TypeId::of::<u8>());
    /// ```
    #[must_use]
    pub fn type_id_of_element(&self) -> TypeId {
        (self.meta.type_id)()
    }

    /// Returns some reference to the original slice if the elements are of
    /// type `T`, or `None` if they are not.
    #[must_use]
    pub fn downcast<T: AnyBound<B>>(&self) -> Option<&[T]> {
        if TypeId::of::<T>() == self.type_id_of_element() {
            let ptr = self.ptr.cast::<T>();
            // SAFETY: just checked that we are pointing to the right type
            // using private interface Metadata
            Some(unsafe { slice::from_raw_parts(ptr, self.len) })
        } else if self.meta.is_deferred() {
            Some(&[])
        } else {
            None
        }
    }
}

/// A type-erased mutable slice.
///
/// Semantically `&mut [dyn Any]`.
///
/// # Examples
/// ```
/// use list_any::SliceAnyMut;
/// let mut data = *b"hello";
/// let mut slice_any: SliceAnyMut = SliceAnyMut::from(&mut data[..]);
/// let new_ref = slice_any.downcast_mut::<u8>().unwrap();
/// new_ref[1] = b'a';
/// assert_eq!(&data, b"hallo");
/// ```
#[derive(Debug)]
pub struct SliceAnyMut<'a, B: ?Sized = dyn Any + Send + Sync> {
    ptr: *mut (),
    meta: &'static Metadata,
    len: usize,
    _marker: PhantomData<&'a mut B>,
}

unsafe impl<'a, B: ?Sized + Send + Sync> Send for SliceAnyMut<'a, B> {}
unsafe impl<'a, B: ?Sized + Sync> Sync for SliceAnyMut<'a, B> {}

impl<'a, B: ?Sized, T: AnyBound<B>> From<&'a mut [T]> for SliceAnyMut<'a, B> {
    fn from(slice: &mut [T]) -> Self {
        let ptr = slice.as_mut_ptr().cast();
        let meta = T::META;
        let len = slice.len();
        Self {
            ptr,
            len,
            meta,
            _marker: PhantomData,
        }
    }
}

impl<'a> SliceAnyMut<'a> {
    /// Create a `SliceAnyMut` with a length of 0, for which downcasting will
    /// always return `None`.
    ///
    /// ```
    /// use list_any::SliceAnyMut;
    /// let mut slice = SliceAnyMut::opaque();
    /// assert_eq!(slice.downcast_mut::<f64>(), None);
    /// assert_eq!(slice.downcast_mut::<u32>(), None);
    /// assert_eq!(slice.downcast_mut::<()>(), None);
    /// ```
    #[must_use]
    pub fn opaque() -> Self {
        let slice: &mut [OpaqueValue] = &mut [];
        Self::from(slice)
    }

    /// Create a `SliceAnyMut` with a length of 0, for which downcasting will
    /// always return `Some`.
    ///
    /// ```
    /// use list_any::SliceAnyMut;
    /// let mut slice = SliceAnyMut::deferred();
    /// assert_eq!(slice.downcast_mut::<f64>(), Some(&mut [][..]));
    /// assert_eq!(slice.downcast_mut::<u32>(), Some(&mut [][..]));
    /// assert_eq!(slice.downcast_mut::<()>(), Some(&mut [][..]));
    /// ```
    #[must_use]
    pub fn deferred() -> Self {
        let slice: &mut [DeferredValue] = &mut [];
        Self::from(slice)
    }
}

impl<'a, B: ?Sized> SliceAnyMut<'a, B> {
    /// Returns the number of elements in the slice.
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the slice has a length of 0.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the `TypeId` of the elements contained in this slice.
    ///
    /// # Examples
    /// ```
    /// use core::any::TypeId;
    /// use list_any::SliceAnyMut;
    /// let mut data = *b"hello";
    /// let slice_any: SliceAnyMut = SliceAnyMut::from(&mut data[..]);
    /// assert_eq!(slice_any.type_id_of_element(), TypeId::of::<u8>());
    /// ```
    #[must_use]
    pub fn type_id_of_element(&self) -> TypeId {
        (self.meta.type_id)()
    }

    /// Returns some mutable reference to the original slice if the elements
    /// are of type `T`, or `None` if they are not.
    #[must_use]
    pub fn downcast_mut<T: AnyBound<B>>(&mut self) -> Option<&mut [T]> {
        if TypeId::of::<T>() == self.type_id_of_element() {
            let ptr = self.ptr.cast::<T>();
            // SAFETY: just checked that we are pointing to the right type
            // using private interface Metadata
            Some(unsafe { slice::from_raw_parts_mut(ptr, self.len) })
        } else if self.meta.is_deferred() {
            Some(&mut [])
        } else {
            None
        }
    }

    /// Returns this [`SliceAnyMut`] as an immutable [`SliceAny`].
    ///
    /// [`SliceAny`]: crate::SliceAny
    #[must_use]
    pub fn as_slice_any(&self) -> SliceAny<'_> {
        SliceAny {
            ptr: self.ptr,
            meta: self.meta,
            len: self.len,
            _marker: PhantomData,
        }
    }
}

/// This trait describes the Send + Sync bounds on the types of elements
/// contained in the lists in this crate.
pub unsafe trait AnyBound<T: ?Sized>: Any {}

unsafe impl<T: Any> AnyBound<dyn Any> for T {}
unsafe impl<T: Any + Send> AnyBound<dyn Any + Send> for T {}
unsafe impl<T: Any + Sync> AnyBound<dyn Any + Sync> for T {}
unsafe impl<T: Any + Send + Sync> AnyBound<dyn Any + Send + Sync> for T {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downcast_slice() {
        let data: &[u8] = b"hello";
        let slice_any: SliceAny = SliceAny::from(data);
        assert_eq!(slice_any.type_id_of_element(), TypeId::of::<u8>());
        assert_eq!(slice_any.downcast::<()>(), None);
        assert_eq!(slice_any.downcast::<u32>(), None);
        assert_eq!(slice_any.downcast::<u8>(), Some(data));
    }

    #[test]
    fn downcast_slice_mut() {
        let mut data = *b"hello";
        let mut slice_any: SliceAnyMut = SliceAnyMut::from(&mut data[..]);
        assert_eq!(slice_any.type_id_of_element(), TypeId::of::<u8>());
        assert_eq!(slice_any.downcast_mut::<()>(), None);
        assert_eq!(slice_any.downcast_mut::<u32>(), None);

        let new_ref = slice_any.downcast_mut::<u8>().unwrap();
        new_ref[1] = b'a';
        assert_eq!(&data, b"hallo");
    }

    #[test]
    fn deferred_slices() {
        let slice = SliceAny::deferred();
        assert_eq!(slice.downcast::<f64>(), Some(&[][..]));
        assert_eq!(slice.downcast::<u32>(), Some(&[][..]));
        assert_eq!(slice.downcast::<()>(), Some(&[][..]));

        let mut slice = SliceAnyMut::deferred();
        assert_eq!(slice.downcast_mut::<f64>(), Some(&mut [][..]));
        assert_eq!(slice.downcast_mut::<u32>(), Some(&mut [][..]));
        assert_eq!(slice.downcast_mut::<()>(), Some(&mut [][..]));
    }
}
