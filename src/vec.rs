/* SPDX-License-Identifier: (Apache-2.0 OR MIT OR Zlib) */
/* Copyright © 2021 Violet Leonard */

#![allow(clippy::module_name_repetitions)]

use core::{
    any::{Any, TypeId},
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    slice,
};

use alloc::vec::Vec;

use super::{
    AnyBound, DeferredValue, HasMetadata, Metadata, OpaqueValue, SliceAny,
    SliceAnyMut,
};

/// # Safety
/// Must be called with pointers formerly obtained from a Vec<T> that was
/// not already dropped
pub(crate) unsafe fn drop<T>(ptr: *mut (), len: usize, cap: usize) {
    Vec::<T>::from_raw_parts(ptr.cast(), len, cap);
}

/// A type-erased [`Vec`](alloc::vec::Vec).
///
/// Semantically `Vec<dyn Any>`.
///
/// # Examples
/// ```
/// use list_any::VecAny;
/// let data: Vec<u8> = b"hello".to_vec();
/// let vec_any: VecAny = VecAny::from(data);
/// let data_returned = vec_any.downcast::<u8>().unwrap();
/// assert_eq!(data_returned, b"hello");
/// ```
#[derive(Debug)]
pub struct VecAny<B: ?Sized = dyn Any + Send + Sync> {
    ptr: *mut (),
    meta: &'static Metadata,
    len: usize,
    cap: usize,
    _marker: PhantomData<B>,
}

unsafe impl<B: ?Sized + Send> Send for VecAny<B> {}
unsafe impl<B: ?Sized + Sync> Sync for VecAny<B> {}

impl<B: ?Sized, T: AnyBound<B>> From<Vec<T>> for VecAny<B> {
    fn from(vec: Vec<T>) -> Self {
        let mut vec = mem::ManuallyDrop::new(vec);
        let ptr = vec.as_mut_ptr().cast();
        let meta = T::META;
        let len = vec.len();
        let cap = vec.capacity();
        Self {
            ptr,
            meta,
            len,
            cap,
            _marker: PhantomData,
        }
    }
}

impl<B: ?Sized> Drop for VecAny<B> {
    fn drop(&mut self) {
        unsafe {
            (self.meta.drop)(self.ptr, self.len, self.cap);
        }
    }
}

impl VecAny {
    /// Create a new, empty, [`VecAny`] for which downcasting will always
    /// return `None`.
    #[must_use]
    pub fn opaque() -> Self {
        Self::new::<OpaqueValue>()
    }

    /// Create a new, empty, [`VecAny`] with a internal type deferred until
    /// the first mutable downcast.  Note that, until this type is otherwise
    /// downcast, [`downcast_slice`](Self::downcast_slice) will always succeed.
    ///
    /// ```
    /// use list_any::VecAny;
    /// let mut v = VecAny::deferred();
    /// assert_eq!(v.downcast_slice::<f64>(), Some(&[][..]));
    /// assert_eq!(v.downcast_slice_mut::<u32>(), Some(&mut [][..]));
    /// assert_eq!(v.downcast_slice::<f64>(), None);
    /// ```
    #[must_use]
    pub fn deferred() -> Self {
        Self::new::<DeferredValue>()
    }
}

impl<B: ?Sized> VecAny<B> {
    /// Create a new, empty, [`VecAny`] with a given internal type.
    #[must_use]
    pub fn new<T: AnyBound<B>>() -> Self {
        Self::from(Vec::<T>::new())
    }

    /// Returns the number of elements in the vector.
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns the number of elements the vector can hold without
    /// reallocating.
    #[must_use]
    pub fn capcaity(&self) -> usize {
        self.cap
    }

    /// Returns `true` if the vector contains no elements.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the `TypeId` of the elements contained within the vector.
    /// ```
    /// use core::any::TypeId;
    /// use list_any::VecAny;
    /// let data: Vec<u8> = b"hello".to_vec();
    /// let vec_any: VecAny = VecAny::from(data);
    /// assert_eq!(vec_any.type_id_of_element(), TypeId::of::<u8>());
    /// ```
    #[must_use]
    pub fn type_id_of_element(&self) -> TypeId {
        (self.meta.type_id)()
    }

    /// Returns a borrow of this [`VecAny`] as a [`SliceAny`].
    #[must_use]
    pub fn as_slice_any(&self) -> SliceAny<'_> {
        SliceAny {
            ptr: self.ptr,
            meta: self.meta,
            len: self.len,
            _marker: PhantomData,
        }
    }

    /// Returns a mutable borrow of this [`VecAny`] as a [`SliceAnyMut`].
    #[must_use]
    pub fn as_slice_any_mut(&mut self) -> SliceAnyMut<'_> {
        SliceAnyMut {
            ptr: self.ptr,
            meta: self.meta,
            len: self.len,
            _marker: PhantomData,
        }
    }

    /// Attempts to downcast this [`VecAny`] to a concrete vector type.
    ///
    /// # Errors
    ///
    /// Returns self unchanged if the [`VecAny`] did not contain elements of
    /// type `T`.
    pub fn downcast<T: AnyBound<B>>(self) -> Result<Vec<T>, Self> {
        if self.type_id_of_element() == TypeId::of::<T>() {
            let this = mem::ManuallyDrop::new(self);
            // SAFETY: just checked that we are pointing to the right type
            // using private interface Metadata
            Ok(unsafe {
                Vec::from_raw_parts(this.ptr.cast(), this.len, this.cap)
            })
        } else if self.meta.is_deferred() {
            // Optimization, Vec of DeferredValue never needs to be dropped
            mem::forget(self);
            Ok(Vec::new())
        } else {
            Err(self)
        }
    }

    /// Returns some mutable guard over the original vector if the elements
    /// are of type `T`, or `None` if they are not.
    ///
    /// Leaking this guard (through [`forget`](core::mem::forget) or similar)
    /// is safe, however it will have the effect of leaking all of the
    /// elements in the vector, and the source [`VecAny`] will be left empty.
    #[must_use]
    pub fn downcast_mut<T: AnyBound<B>>(
        &mut self,
    ) -> Option<VecAnyGuard<'_, T, B>> {
        if self.type_id_of_element() == TypeId::of::<T>() {
            // SAFETY: just checked that we are pointing to the right type
            // using private interface Metadata
            let vec = unsafe { self.swap_vec(Vec::new()) };
            Some(VecAnyGuard { vec, origin: self })
        } else if self.meta.is_deferred() {
            // Optimization, Vec of DeferredValue never needs to be dropped
            mem::forget(mem::replace(self, Self::new::<T>()));
            // SAFETY: just inserted a vec of the right type
            let vec = unsafe { self.swap_vec(Vec::new()) };
            Some(VecAnyGuard { vec, origin: self })
        } else {
            None
        }
    }

    /// Returns some reference to the contained vector as a slice if the
    /// contained elements are of type `T`, or `None` if they are not.
    #[must_use]
    pub fn downcast_slice<T: AnyBound<B>>(&self) -> Option<&[T]> {
        if self.type_id_of_element() == TypeId::of::<T>() {
            // SAFETY: just checked that we are pointing to the right type
            // using private interface Metadata
            Some(unsafe { slice::from_raw_parts(self.ptr.cast(), self.len) })
        } else if self.meta.is_deferred() {
            Some(&[])
        } else {
            None
        }
    }

    /// Returns some mutable reference to the contained vector as a slice if
    /// the contained elements are of type `T`, or `None` if they are not.
    #[must_use]
    pub fn downcast_slice_mut<T: AnyBound<B>>(&mut self) -> Option<&mut [T]> {
        if self.type_id_of_element() == TypeId::of::<T>() {
            // SAFETY: just checked that we are pointing to the right type
            // using private interface Metadata
            Some(unsafe {
                slice::from_raw_parts_mut(self.ptr.cast(), self.len)
            })
        } else if self.meta.is_deferred() {
            // Optimization, Vec of DeferredValue never needs to be dropped
            mem::forget(mem::replace(self, Self::new::<T>()));
            // SAFETY: just inserted a vec of the right type
            Some(unsafe {
                slice::from_raw_parts_mut(self.ptr.cast(), self.len)
            })
        } else {
            None
        }
    }

    /// # Safety
    /// This `VecAny` must be guaranteed to have the element type T
    unsafe fn swap_vec<T: AnyBound<B>>(&mut self, new: Vec<T>) -> Vec<T> {
        let mut new = mem::ManuallyDrop::new(new);
        let mut ptr = new.as_mut_ptr().cast();
        let mut len = new.len();
        let mut cap = new.capacity();
        mem::swap(&mut self.ptr, &mut ptr);
        mem::swap(&mut self.len, &mut len);
        mem::swap(&mut self.cap, &mut cap);
        // SAFETY: these values came from us, and we always leave ourself in
        // a valid state
        Vec::from_raw_parts(ptr.cast(), len, cap)
    }
}

/// A guard providing mutable access to a concretely typed vector, obtained
/// with [`VecAny::downcast_mut`].
///
/// Leaking this guard (through [`forget`](core::mem::forget) or similar)
/// is safe, however it will have the effect of leaking all of the
/// elements in the vector, and the source [`VecAny`] will be left empty.
#[derive(Debug)]
pub struct VecAnyGuard<'a, T: AnyBound<B>, B: ?Sized = dyn Any + Send + Sync> {
    vec: Vec<T>,
    origin: &'a mut VecAny<B>,
}

impl<'a, T: AnyBound<B>, B: ?Sized> Deref for VecAnyGuard<'a, T, B> {
    type Target = Vec<T>;

    fn deref(&self) -> &Vec<T> {
        &self.vec
    }
}

impl<'a, T: AnyBound<B>, B: ?Sized> DerefMut for VecAnyGuard<'a, T, B> {
    fn deref_mut(&mut self) -> &mut Vec<T> {
        &mut self.vec
    }
}

impl<'a, T: AnyBound<B>, B: ?Sized> Drop for VecAnyGuard<'a, T, B> {
    fn drop(&mut self) {
        // SAFETY: VecAnyGuard is only constructed with a valid T for
        // the VecAny
        unsafe {
            self.origin.swap_vec(mem::take(&mut self.vec));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downcast_vec() {
        use alloc::vec::Vec;

        let data: Vec<u8> = b"hello".to_vec();
        let mut vec_any: VecAny = VecAny::from(data);

        assert_eq!(vec_any.type_id_of_element(), TypeId::of::<u8>());

        assert!(vec_any.downcast_mut::<()>().is_none());
        assert!(vec_any.downcast_mut::<u32>().is_none());
        assert!(vec_any.downcast_mut::<u8>().is_some());

        assert_eq!(vec_any.downcast_slice::<()>(), None);
        assert_eq!(vec_any.downcast_slice::<u32>(), None);
        assert_eq!(vec_any.downcast_slice::<u8>(), Some(&b"hello"[..]));

        let vec_any = vec_any.downcast::<()>().unwrap_err();
        let vec_any = vec_any.downcast::<u32>().unwrap_err();
        let data = vec_any.downcast::<u8>().unwrap();
        assert_eq!(data, b"hello".to_vec());
    }

    #[test]
    fn deferred_vec() {
        let mut v = VecAny::deferred();
        assert_eq!(v.downcast_slice::<f64>(), Some(&[][..]));
        assert_eq!(v.downcast_slice_mut::<u32>(), Some(&mut [][..]));
        assert_eq!(v.downcast_slice::<f64>(), None);
    }
}
