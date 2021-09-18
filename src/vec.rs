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
    AnyBound, DefaultValue, HasMetadata, Metadata, SliceAny, SliceAnyMut,
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

impl Default for VecAny {
    /// Create a `VecAny` with a length of 0, for which downcasting will
    /// always return `None`.
    fn default() -> Self {
        Self::new::<DefaultValue>()
    }
}

impl<B: ?Sized, T: AnyBound<B>> From<Vec<T>> for VecAny<B> {
    fn from(vec: Vec<T>) -> Self {
        let mut vec = mem::ManuallyDrop::new(vec);
        let ptr = vec.as_mut_ptr().cast();
        let meta = &T::META;
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
    pub fn downcast<T: Any>(self) -> Result<Vec<T>, Self> {
        if self.type_id_of_element() == TypeId::of::<T>() {
            let this = mem::ManuallyDrop::new(self);
            // SAFETY: just checked that we are pointing to the right type
            // using private interface Metadata
            Ok(unsafe {
                Vec::from_raw_parts(this.ptr.cast(), this.len, this.cap)
            })
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
    pub fn downcast_mut<T: Any>(&mut self) -> Option<VecAnyGuard<'_, T, B>> {
        (self.type_id_of_element() == TypeId::of::<T>()).then(move || {
            // SAFETY: just checked that we are pointing to the right type
            // using private interface Metadata
            let vec = unsafe { self.swap_vec(Vec::new()) };
            VecAnyGuard { vec, origin: self }
        })
    }

    /// Returns some reference to the contained vector as a slice if the
    /// contained elements are of type `T`, or `None` if they are not.
    #[must_use]
    pub fn downcast_slice<T: Any>(&self) -> Option<&[T]> {
        (self.type_id_of_element() == TypeId::of::<T>()).then(|| {
            // SAFETY: just checked that we are pointing to the right type
            // using private interface Metadata
            unsafe { slice::from_raw_parts(self.ptr.cast(), self.len) }
        })
    }

    /// Returns some mutable reference to the contained vector as a slice if
    /// the contained elements are of type `T`, or `None` if they are not.
    #[must_use]
    pub fn downcast_slice_mut<T: Any>(&mut self) -> Option<&mut [T]> {
        (self.type_id_of_element() == TypeId::of::<T>()).then(|| {
            // SAFETY: just checked that we are pointing to the right type
            // using private interface Metadata
            unsafe { slice::from_raw_parts_mut(self.ptr.cast(), self.len) }
        })
    }

    /// # Safety
    /// This `VecAny` must be guaranteed to have the element type T
    unsafe fn swap_vec<T: Any>(&mut self, new: Vec<T>) -> Vec<T> {
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
pub struct VecAnyGuard<'a, T: Any, B: ?Sized = dyn Any + Send + Sync> {
    vec: Vec<T>,
    origin: &'a mut VecAny<B>,
}

impl<'a, T: Any, B: ?Sized> Deref for VecAnyGuard<'a, T, B> {
    type Target = Vec<T>;

    fn deref(&self) -> &Vec<T> {
        &self.vec
    }
}

impl<'a, T: Any, B: ?Sized> DerefMut for VecAnyGuard<'a, T, B> {
    fn deref_mut(&mut self) -> &mut Vec<T> {
        &mut self.vec
    }
}

impl<'a, T: Any, B: ?Sized> Drop for VecAnyGuard<'a, T, B> {
    fn drop(&mut self) {
        // SAFETY: VecAnyGuard is only constructed with a valid T for
        // the VecAny
        unsafe {
            self.origin.swap_vec(mem::take(&mut self.vec));
        }
    }
}
