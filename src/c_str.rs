// Copyright 2014 Mikhail Zabaluev <mikhail.zabaluev@gmail.com>
// Copyright 2012 The Rust Project Developers
// See the COPYRIGHT file at the top-level directory of this distribution
// and at http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!

C-string manipulation and management

This modules provides the basic methods for creating and manipulating
null-terminated strings for use with FFI calls (back to C). Most C APIs require
that the string being passed to them is null-terminated, and by default rust's
string types are *not* null terminated.

The other problem with translating Rust strings to C strings is that Rust
strings can validly contain a null-byte in the middle of the string (0 is a
valid Unicode codepoint). This means that not all Rust strings can actually be
translated to C strings.

# Creation of a C string

A C string is managed through the types `CString` and `CStrBuf` defined
in this module. Values of these types "own" an internal buffer of characters
and will call a destructor closure when the string is dropped.
The `ToCStr` trait is implemented for `&str` and `&[u8]`, but the conversions
can fail due to some of the limitations explained above.

This also means that currently whenever a C string is created, an allocation
must be performed to place the data elsewhere (the lifetime of the C string is
not tied to the lifetime of the original string/data buffer). If C strings are
heavily used in applications, then caching may be advisable to prevent
unnecessary amounts of allocations.

An example of creating and using a C string would be:

```rust
extern crate libc;

extern {
    fn puts(s: *const libc::c_char);
}

fn main() {
    let my_string = "Hello, world!";

    // Allocate the C string with an explicit local that owns the string. The
    // `c_buffer` pointer will be deallocated when `my_c_string` goes out of scope.
    let my_c_string = my_string.to_c_str();
    unsafe {
        puts(my_c_string.as_ptr());
    }

    // Don't save/return the pointer to the C string, the `c_buffer` will be
    // deallocated when this block returns!
    my_string.with_c_str(|c_buffer| {
        unsafe { puts(c_buffer); }
    });
}
```

*/

#![no_implicit_prelude]

use std::fmt;
use std::hash;
use std::kinds::{Send,Sized,marker};
use std::mem;
use std::prelude::{Drop, Eq, ImmutablePartialEqSlice};
use std::prelude::{ImmutableSlice, Iterator};
use std::prelude::{None, Option, Ord, Ordering, PartialEq};
use std::prelude::{PartialOrd, RawPtr, Some, StrSlice};
use std::ptr;
use std::raw::Slice;
use std::slice;
use std::str;
use std::string;
use std::string::String;
use libc;

const NUL: u8 = 0;

/// A low-level representation of a C String.
///
/// This structure wraps a raw pointer to a NUL-terminated C string,
/// and will optionally invoke a destructor closure when it goes
/// out of scope.
///
/// For performance reasons, `CStrBuf` does not provide operations that
/// require calculation of the string's length. To get those, promote a
/// `CStrBuf` into `CString` using the method `.into_c_str()`.
pub struct CStrBuf {
    ptr: *const libc::c_char,
    dtor: Option<proc(*const libc::c_char):Send>
}

/// A length-aware representation of a C string.
///
/// This structure builds upon `CStrBuf` to add the computed string length.
/// References to `CString` values can be converted to byte or string slices
/// at constant cost.
pub struct CString {
    buf: CStrBuf,
    len: uint
}

impl PartialEq for CStrBuf {
    fn eq(&self, other: &CStrBuf) -> bool {
        unsafe { libc::strcmp(self.ptr, other.ptr) == 0 }
    }
}

impl PartialOrd for CStrBuf {
    #[inline]
    fn partial_cmp(&self, other: &CStrBuf) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CStrBuf {
    fn cmp(&self, other: &CStrBuf) -> Ordering {
        let res = unsafe { libc::strcmp(self.ptr, other.ptr) as int };
        res.cmp(&0)
    }
}

impl Eq for CStrBuf {}

impl PartialEq for CString {
    #[inline]
    fn eq(&self, other: &CString) -> bool {
        self.as_bytes().eq(&other.as_bytes())
    }
}

impl PartialOrd for CString {
    #[inline]
    fn partial_cmp(&self, other: &CString) -> Option<Ordering> {
        self.as_bytes().partial_cmp(&other.as_bytes())
    }
}

impl Ord for CString {
    #[inline]
    fn cmp(&self, other: &CString) -> Ordering {
        self.as_bytes().cmp(&other.as_bytes())
    }
}

impl Eq for CString {}

impl<S: hash::Writer> hash::Hash<S> for CString {
    #[inline]
    fn hash(&self, state: &mut S) {
        self.as_bytes().hash(state)
    }
}

fn libc_malloc(size: uint) -> *mut libc::c_char {
    let buf = unsafe {
            libc::malloc(size as libc::size_t) as *mut libc::c_char
        };
    if buf.is_null() { ::alloc::oom() }
    buf
}

fn libc_free(buf: *const libc::c_char) {
    unsafe { libc::free(buf as *mut libc::c_void); }
}

impl CStrBuf {

    unsafe fn new_internal(ptr: *const libc::c_char,
                           maybe_dtor: Option<proc(*const libc::c_char):Send>)
                          -> CStrBuf {
        assert!(!ptr.is_null());
        CStrBuf { ptr: ptr, dtor: maybe_dtor }
    }

    /// Create a `CStrBuf` from a pointer. The returned `CStrBuf` will not
    /// deallocate the string when dropped.
    ///
    ///# Failure
    ///
    /// Fails if `ptr` is null.
    pub unsafe fn new_unowned(ptr: *const libc::c_char) -> CStrBuf {
        CStrBuf::new_internal(ptr, None)
    }

    /// Create a `CStrBuf` from a pointer. The returned `CStrBuf` will
    /// deallocate the string with the standard C function `free()`
    /// when dropped.
    ///
    ///# Failure
    ///
    /// Fails if `ptr` is null.
    pub unsafe fn new_libc(ptr: *const libc::c_char) -> CStrBuf {
        CStrBuf::new_with_dtor(ptr, libc_free)
    }

    /// Create a `CStrBuf` from a foreign pointer and a closure to run
    /// upon destruction.
    ///
    ///# Failure
    ///
    /// Fails if `ptr` is null.
    pub unsafe fn new_with_dtor(ptr: *const libc::c_char,
                                dtor: proc(*const libc::c_char):Send)
                               -> CStrBuf {
        CStrBuf::new_internal(ptr, Some(dtor))
    }

    /// Promote the `CStrBuf` into `CString` by calculating the string's
    /// length.
    pub fn into_c_str(mut self) -> CString {
        CString {
            buf: CStrBuf { ptr: self.ptr, dtor: self.dtor.take() },
            len: unsafe { libc::strlen(self.ptr) as uint }
        }
    }

    /// Copies the `CStrBuf` into a `String`.
    /// Returns `None` if the string is not UTF-8.
    pub fn to_string(&self) -> Option<String> {
        unsafe {
            let len = libc::strlen(self.ptr) as uint;
            let ptr = self.ptr as *const u8;
            if slice::raw::buf_as_slice(ptr, len, |v| { str::is_utf8(v) }) {
                Some(string::raw::from_buf_len(ptr, len))
            } else {
                None
            }
        }
    }

    /// Return a pointer to the NUL-terminated string data.
    ///
    /// `.as_ptr` returns an internal pointer into the `CStrBuf`, and
    /// may be invalidated when the `CStrBuf` falls out of scope (the
    /// destructor will run, freeing the allocation if there is
    /// one).
    pub fn as_ptr(&self) -> *const libc::c_char {
        self.ptr
    }

    /// Returns an iterator over the string's bytes.
    pub fn iter<'a>(&'a self) -> CChars<'a> {
        CChars {
            ptr: self.ptr,
            marker: marker::ContravariantLifetime,
        }
    }

    /// Unwraps the wrapped `*libc::c_char` from the `CStrBuf` wrapper
    /// without running the destructor. If the string was allocated,
    /// a user of `.unwrap()` should ensure the allocation is eventually
    /// freed.
    ///
    /// Prefer `.as_ptr()` when just retrieving a pointer to the
    /// string data, as that does not relinquish ownership.
    pub unsafe fn unwrap(mut self) -> *const libc::c_char {
        self.dtor = None;
        self.ptr
    }

    /// Returns true if the wrapped string is empty.
    pub fn is_empty(&self) -> bool { unsafe { *self.ptr == 0 } }
}

impl CString {

    unsafe fn new_internal(ptr: *const libc::c_char,
                           len: uint,
                           maybe_dtor: Option<proc(*const libc::c_char):Send>)
                          -> CString {
        assert!(!ptr.is_null());
        assert!(*ptr.offset(len as int) == (NUL as libc::c_char));
        CString { buf: CStrBuf::new_internal(ptr, maybe_dtor), len: len }
    }

    /// Create a `CString` from a pointer and pre-calculated length
    /// (not including the terminating NUL).
    /// The returned `CString` will not deallocate the string when dropped.
    ///
    ///# Failure
    ///
    /// Fails if `ptr` is null, or if the byte at `len` is not NUL.
    pub unsafe fn new_unowned(ptr: *const libc::c_char, len: uint) -> CString {
        CString::new_internal(ptr, len, None)
    }

    /// Create a `CString` from a pointer and pre-calculated length
    /// (not including the terminating NUL).
    /// The returned `CString` will deallocate the string with the standard
    /// C function `free()` when dropped.
    ///
    ///# Failure
    ///
    /// Fails if `ptr` is null, or if the byte at `len` is not NUL.
    pub unsafe fn new_libc(ptr: *const libc::c_char, len: uint) -> CString {
        CString::new_with_dtor(ptr, len, libc_free)
    }

    /// Create a `CString` from a foreign pointer, a pre-calculated length
    /// (not including the terminating NUL), and a closure to run upon
    /// destruction.
    ///
    ///# Failure
    ///
    /// Fails if `ptr` is null, or if the byte at `len` is not NUL.
    pub unsafe fn new_with_dtor(ptr: *const libc::c_char,
                                len: uint,
                                dtor: proc(*const libc::c_char):Send)
                               -> CString {
        CString::new_internal(ptr, len, Some(dtor))
    }

    /// Return a pointer to the NUL-terminated string data.
    ///
    /// `.as_ptr` returns an internal pointer into the `CString`, and
    /// may be invalidated when the `CString` falls out of scope (the
    /// destructor will run, freeing the allocation if there is
    /// one).
    ///
    /// ```rust
    /// let foo = "some string";
    ///
    /// // right
    /// let x = foo.to_c_str();
    /// let p = x.as_ptr();
    ///
    /// // wrong (the CString will be freed, invalidating `p`)
    /// let p = foo.to_c_str().as_ptr();
    /// ```
    ///
    /// # Example
    ///
    /// ```rust
    /// extern crate libc;
    ///
    /// fn main() {
    ///     let c_str = "foo bar".to_c_str();
    ///     unsafe {
    ///         libc::puts(c_str.as_ptr());
    ///     }
    /// }
    /// ```
    pub fn as_ptr(&self) -> *const libc::c_char {
        self.buf.as_ptr()
    }

    /// Converts the `CString` into a `&[u8]` without copying.
    /// Includes the terminating NUL byte.
    #[inline]
    pub fn as_bytes<'a>(&'a self) -> &'a [u8] {
        unsafe {
            mem::transmute(Slice { data: self.buf.ptr, len: self.len + 1 })
        }
    }

    /// Converts the `CString` into a `&[u8]` without copying.
    /// Does not include the terminating NUL byte.
    #[inline]
    pub fn as_bytes_no_nul<'a>(&'a self) -> &'a [u8] {
        unsafe {
            mem::transmute(Slice { data: self.buf.ptr, len: self.len })
        }
    }

    /// Converts the `CString` into a `&str` without copying.
    /// Returns `None` if the string is not UTF-8.
    #[inline]
    pub fn as_str<'a>(&'a self) -> Option<&'a str> {
        let buf = self.as_bytes_no_nul();
        str::from_utf8(buf)
    }

    /// Returns an iterator over the string's bytes.
    pub fn iter<'a>(&'a self) -> CChars<'a> {
        self.buf.iter()
    }

    /// Unwraps the wrapped `*libc::c_char` from the `CString` wrapper
    /// without running the destructor. If the string was allocated,
    /// a user of `.unwrap()` should ensure the allocation is eventually
    /// freed.
    ///
    /// Prefer `.as_ptr()` when just retrieving a pointer to the
    /// string data, as that does not relinquish ownership.
    pub unsafe fn unwrap(self) -> *const libc::c_char {
        self.buf.unwrap()
    }

    /// Return the number of bytes in the CString
    /// (not including the NUL terminator).
    pub fn len(&self) -> uint { self.len }

    /// Returns true if the string is empty.
    pub fn is_empty(&self) -> bool { self.len == 0 }
}

impl Drop for CStrBuf {
    fn drop(&mut self) {
        match self.dtor.take() {
            None => (),
            Some(f) => f(self.ptr)
        }
    }
}

impl fmt::Show for CString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        String::from_utf8_lossy(self.as_bytes_no_nul()).fmt(f)
    }
}

/// A generic trait for converting a value to a CString.
pub trait ToCStr for Sized? {
    /// Copy the receiver into a CString.
    ///
    /// # Failure
    ///
    /// Fails the task if the receiver has an interior null.
    fn to_c_str(&self) -> CString;

    /// Unsafe variant of `to_c_str()` that doesn't check for nulls.
    unsafe fn to_c_str_unchecked(&self) -> CString;

    /// Work with a temporary CString constructed from the receiver.
    /// The provided `*libc::c_char` will be freed immediately upon return.
    ///
    /// # Example
    ///
    /// ```rust
    /// extern crate libc;
    ///
    /// fn main() {
    ///     let s = "PATH".with_c_str(|path| unsafe {
    ///         libc::getenv(path)
    ///     });
    /// }
    /// ```
    ///
    /// # Failure
    ///
    /// Fails the task if the receiver has an interior null.
    #[inline]
    fn with_c_str<T>(&self, f: |*const libc::c_char| -> T) -> T {
        let c_str = self.to_c_str();
        f(c_str.as_ptr())
    }

    /// Unsafe variant of `with_c_str()` that doesn't check for nulls.
    #[inline]
    unsafe fn with_c_str_unchecked<T>(&self, f: |*const libc::c_char| -> T) -> T {
        let c_str = self.to_c_str_unchecked();
        f(c_str.as_ptr())
    }
}

impl ToCStr for str {
    #[inline]
    fn to_c_str(&self) -> CString {
        self.as_bytes().to_c_str()
    }

    #[inline]
    unsafe fn to_c_str_unchecked(&self) -> CString {
        self.as_bytes().to_c_str_unchecked()
    }

    #[inline]
    fn with_c_str<T>(&self, f: |*const libc::c_char| -> T) -> T {
        self.as_bytes().with_c_str(f)
    }

    #[inline]
    unsafe fn with_c_str_unchecked<T>(&self, f: |*const libc::c_char| -> T) -> T {
        self.as_bytes().with_c_str_unchecked(f)
    }
}

impl ToCStr for String {
    #[inline]
    fn to_c_str(&self) -> CString {
        self.as_bytes().to_c_str()
    }

    #[inline]
    unsafe fn to_c_str_unchecked(&self) -> CString {
        self.as_bytes().to_c_str_unchecked()
    }

    #[inline]
    fn with_c_str<T>(&self, f: |*const libc::c_char| -> T) -> T {
        self.as_bytes().with_c_str(f)
    }

    #[inline]
    unsafe fn with_c_str_unchecked<T>(&self, f: |*const libc::c_char| -> T) -> T {
        self.as_bytes().with_c_str_unchecked(f)
    }
}

// The length of the stack allocated buffer for `vec.with_c_str()`
const BUF_LEN: uint = 128;

impl<'a> ToCStr for [u8] {
    fn to_c_str(&self) -> CString {
        assert!(!self.contains(&NUL));
        unsafe { self.to_c_str_unchecked() }
    }

    unsafe fn to_c_str_unchecked(&self) -> CString {
        str_dup(self.as_ptr(), self.len())
    }

    fn with_c_str<T>(&self, f: |*const libc::c_char| -> T) -> T {
        unsafe { with_c_str(self, true, f) }
    }

    unsafe fn with_c_str_unchecked<T>(&self, f: |*const libc::c_char| -> T) -> T {
        with_c_str(self, false, f)
    }
}

impl<'a, Sized? T: ToCStr> ToCStr for &'a T {
    #[inline]
    fn to_c_str(&self) -> CString {
        (**self).to_c_str()
    }

    #[inline]
    unsafe fn to_c_str_unchecked(&self) -> CString {
        (**self).to_c_str_unchecked()
    }

    #[inline]
    fn with_c_str<T>(&self, f: |*const libc::c_char| -> T) -> T {
        (**self).with_c_str(f)
    }

    #[inline]
    unsafe fn with_c_str_unchecked<T>(&self, f: |*const libc::c_char| -> T) -> T {
        (**self).with_c_str_unchecked(f)
    }
}

unsafe fn buf_dup(ptr: *const u8, len: uint) -> CStrBuf {
    let copy = libc_malloc(len + 1);

    ptr::copy_nonoverlapping_memory(copy,
            ptr as *const libc::c_char, len);
    *copy.offset(len as int) = 0;

    CStrBuf::new_libc(copy as *const libc::c_char)
}

unsafe fn str_dup(ptr: *const u8, len: uint) -> CString {
    CString { buf: buf_dup(ptr, len), len: len }
}

// Unsafe function that handles possibly copying the &[u8] into a stack array.
unsafe fn with_c_str<T>(v: &[u8], checked: bool,
                        f: |*const libc::c_char| -> T) -> T {
    let c_str = if v.len() < BUF_LEN {
        if checked {
            assert!(!v.contains(&NUL));
        }
        let mut buf: [u8, .. BUF_LEN] = mem::uninitialized();
        slice::bytes::copy_memory(buf, v);
        buf[v.len()] = 0;

        return f(buf.as_ptr() as *const libc::c_char)
    } else if checked {
        v.to_c_str()
    } else {
        v.to_c_str_unchecked()
    };

    f(c_str.as_ptr())
}

impl ToCStr for CStrBuf {

    #[inline]
    fn to_c_str(&self) -> CString {
        unsafe { self.to_c_str_unchecked() }
    }

    unsafe fn to_c_str_unchecked(&self) -> CString {
        str_dup(self.ptr as *const u8, libc::strlen(self.ptr) as uint)
    }

    fn with_c_str<T>(&self, f: |*const libc::c_char| -> T) -> T {
        f(self.ptr)
    }

    unsafe fn with_c_str_unchecked<T>(&self, f: |*const libc::c_char| -> T) -> T {
        f(self.ptr)
    }
}

impl ToCStr for CString {

    #[inline]
    fn to_c_str(&self) -> CString {
        unsafe { self.to_c_str_unchecked() }
    }

    unsafe fn to_c_str_unchecked(&self) -> CString {
        str_dup(self.buf.ptr as *const u8, self.len)
    }

    fn with_c_str<T>(&self, f: |*const libc::c_char| -> T) -> T {
        self.buf.with_c_str(f)
    }

    unsafe fn with_c_str_unchecked<T>(&self, f: |*const libc::c_char| -> T) -> T {
        self.buf.with_c_str_unchecked(f)
    }
}

/// External iterator for C string's bytes.
///
/// The iteration stops when the terminating NUL byte is reached, without
/// returning the NUL.
///
/// Use with the `std::iter` module.
pub struct CChars<'a> {
    ptr: *const libc::c_char,
    marker: marker::ContravariantLifetime<'a>,
}

impl<'a> Iterator<libc::c_char> for CChars<'a> {
    fn next(&mut self) -> Option<libc::c_char> {
        let ch = unsafe { *self.ptr };
        if ch == 0 {
            None
        } else {
            self.ptr = unsafe { self.ptr.offset(1) };
            Some(ch)
        }
    }
}

/// Parses a C "multistring", eg windows env values or
/// the req->ptr result in a uv_fs_readdir() call.
///
/// Optionally, a `count` can be passed in, limiting the
/// parsing to only being done `count`-times.
///
/// The specified closure is invoked with each string that
/// is found, and the number of strings found is returned.
pub unsafe fn from_c_multistring(buf: *const libc::c_char,
                                 count: Option<uint>,
                                 f: |&CString|) -> uint {

    let mut curr_ptr = buf;
    let mut ctr = 0;
    let (limited_count, limit) = match count {
        Some(limit) => (true, limit),
        None => (false, 0)
    };
    while (!limited_count || ctr < limit)
          && *curr_ptr != 0 {
        let cstr = CStrBuf::new_unowned(curr_ptr).into_c_str();
        f(&cstr);
        curr_ptr = curr_ptr.offset(cstr.len() as int + 1);
        ctr += 1;
    }
    return ctr;
}

#[cfg(test)]
mod tests {
    use std::iter::Iterator;
    use std::option::{None,Some};
    use std::ptr;
    use std::ptr::RawPtr;
    use std::slice::ImmutableSlice;
    use std::str::StrSlice;
    use std::string::String;
    use std::task;
    use libc;

    use super::{CStrBuf,CString,ToCStr};
    use super::from_c_multistring;
    use super::buf_dup;

    fn c_buf_from_bytes(v: &[u8]) -> CStrBuf {
        unsafe { buf_dup(v.as_ptr(), v.len()) }
    }

    #[test]
    fn test_str_multistring_parsing() {
        unsafe {
            let input = b"zero\0one\0\0";
            let ptr = input.as_ptr();
            let expected = ["zero", "one"];
            let mut it = expected.iter();
            let result = from_c_multistring(ptr as *const libc::c_char, None, |c| {
                let cbytes = c.as_bytes_no_nul();
                assert_eq!(cbytes, it.next().unwrap().as_bytes());
            });
            assert_eq!(result, 2);
            assert!(it.next().is_none());
        }
    }

    #[test]
    fn test_str_to_c_str() {
        let c_str = "".to_c_str();
        unsafe {
            assert_eq!(*c_str.as_ptr().offset(0), 0);
        }

        let c_str = "hello".to_c_str();
        let buf = c_str.as_ptr();
        unsafe {
            assert_eq!(*buf.offset(0), 'h' as libc::c_char);
            assert_eq!(*buf.offset(1), 'e' as libc::c_char);
            assert_eq!(*buf.offset(2), 'l' as libc::c_char);
            assert_eq!(*buf.offset(3), 'l' as libc::c_char);
            assert_eq!(*buf.offset(4), 'o' as libc::c_char);
            assert_eq!(*buf.offset(5), 0);
        }
    }

    #[test]
    fn test_vec_to_c_str() {
        let b: &[u8] = [];
        let c_str = b.to_c_str();
        unsafe {
            assert_eq!(*c_str.as_ptr().offset(0), 0);
        }

        let c_str = b"hello".to_c_str();
        let buf = c_str.as_ptr();
        unsafe {
            assert_eq!(*buf.offset(0), 'h' as libc::c_char);
            assert_eq!(*buf.offset(1), 'e' as libc::c_char);
            assert_eq!(*buf.offset(2), 'l' as libc::c_char);
            assert_eq!(*buf.offset(3), 'l' as libc::c_char);
            assert_eq!(*buf.offset(4), 'o' as libc::c_char);
            assert_eq!(*buf.offset(5), 0);
        }

        let c_str = b"foo\xFF".to_c_str();
        let buf = c_str.as_ptr();
        unsafe {
            assert_eq!(*buf.offset(0), 'f' as libc::c_char);
            assert_eq!(*buf.offset(1), 'o' as libc::c_char);
            assert_eq!(*buf.offset(2), 'o' as libc::c_char);
            assert_eq!(*buf.offset(3), 0xffu8 as i8);
            assert_eq!(*buf.offset(4), 0);
        }
    }

    #[test]
    fn test_c_buf_to_c_str() {
        let c_buf = c_buf_from_bytes(b"");
        let c_str = c_buf.to_c_str();
        unsafe {
            assert_eq!(*c_str.as_ptr().offset(0), 0);
        }

        let c_buf = c_buf_from_bytes(b"hello");
        let c_str = c_buf.to_c_str();
        let buf = c_str.as_ptr();
        unsafe {
            assert_eq!(*buf.offset(0), 'h' as libc::c_char);
            assert_eq!(*buf.offset(1), 'e' as libc::c_char);
            assert_eq!(*buf.offset(2), 'l' as libc::c_char);
            assert_eq!(*buf.offset(3), 'l' as libc::c_char);
            assert_eq!(*buf.offset(4), 'o' as libc::c_char);
            assert_eq!(*buf.offset(5), 0);
        }

        let c_buf = c_buf_from_bytes(b"foo\xFF");
        let c_str = c_buf.to_c_str();
        let buf = c_str.as_ptr();
        unsafe {
            assert_eq!(*buf.offset(0), 'f' as libc::c_char);
            assert_eq!(*buf.offset(1), 'o' as libc::c_char);
            assert_eq!(*buf.offset(2), 'o' as libc::c_char);
            assert_eq!(*buf.offset(3), 0xffu8 as i8);
            assert_eq!(*buf.offset(4), 0);
        }
    }

    #[test]
    fn test_c_str_to_c_str() {
        let c_str = b"".to_c_str();
        let c_str = c_str.to_c_str();
        unsafe {
            assert_eq!(*c_str.as_ptr().offset(0), 0);
        }

        let c_str = b"hello".to_c_str();
        let c_str = c_str.to_c_str();
        let buf = c_str.as_ptr();
        unsafe {
            assert_eq!(*buf.offset(0), 'h' as libc::c_char);
            assert_eq!(*buf.offset(1), 'e' as libc::c_char);
            assert_eq!(*buf.offset(2), 'l' as libc::c_char);
            assert_eq!(*buf.offset(3), 'l' as libc::c_char);
            assert_eq!(*buf.offset(4), 'o' as libc::c_char);
            assert_eq!(*buf.offset(5), 0);
        }

        let c_str = b"foo\xFF".to_c_str();
        let c_str = c_str.to_c_str();
        let buf = c_str.as_ptr();
        unsafe {
            assert_eq!(*buf.offset(0), 'f' as libc::c_char);
            assert_eq!(*buf.offset(1), 'o' as libc::c_char);
            assert_eq!(*buf.offset(2), 'o' as libc::c_char);
            assert_eq!(*buf.offset(3), 0xffu8 as i8);
            assert_eq!(*buf.offset(4), 0);
        }
    }

    #[test]
    fn test_unwrap() {
        let c_str = "hello".to_c_str();
        unsafe { libc::free(c_str.unwrap() as *mut libc::c_void) }
    }

    #[test]
    fn test_as_ptr() {
        let c_str = "hello".to_c_str();
        let len = unsafe { libc::strlen(c_str.as_ptr()) };
        assert_eq!(len, 5);
    }

    #[test]
    fn test_iterator() {
        let c_str = "".to_c_str();
        let mut iter = c_str.iter();
        assert_eq!(iter.next(), None);

        let c_str = "hello".to_c_str();
        let mut iter = c_str.iter();
        assert_eq!(iter.next(), Some('h' as libc::c_char));
        assert_eq!(iter.next(), Some('e' as libc::c_char));
        assert_eq!(iter.next(), Some('l' as libc::c_char));
        assert_eq!(iter.next(), Some('l' as libc::c_char));
        assert_eq!(iter.next(), Some('o' as libc::c_char));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_to_c_str_fail() {
        assert!(task::try(proc() { "he\x00llo".to_c_str() }).is_err());
    }

    #[test]
    fn test_to_c_str_unchecked() {
        unsafe {
            let c_string = "he\x00llo".to_c_str_unchecked();
            let buf = c_string.as_ptr();
            assert_eq!(*buf.offset(0), 'h' as libc::c_char);
            assert_eq!(*buf.offset(1), 'e' as libc::c_char);
            assert_eq!(*buf.offset(2), 0);
            assert_eq!(*buf.offset(3), 'l' as libc::c_char);
            assert_eq!(*buf.offset(4), 'l' as libc::c_char);
            assert_eq!(*buf.offset(5), 'o' as libc::c_char);
            assert_eq!(*buf.offset(6), 0);
        }
    }

    #[test]
    fn test_as_bytes() {
        let c_str = "hello".to_c_str();
        assert_eq!(c_str.as_bytes(), b"hello\0");
        let c_str = "".to_c_str();
        assert_eq!(c_str.as_bytes(), b"\0");
        let c_str = b"foo\xFF".to_c_str();
        assert_eq!(c_str.as_bytes(), b"foo\xFF\0");
    }

    #[test]
    fn test_as_bytes_no_nul() {
        let c_str = "hello".to_c_str();
        assert_eq!(c_str.as_bytes_no_nul(), b"hello");
        let c_str = "".to_c_str();
        let exp: &[u8] = [];
        assert_eq!(c_str.as_bytes_no_nul(), exp);
        let c_str = b"foo\xFF".to_c_str();
        assert_eq!(c_str.as_bytes_no_nul(), b"foo\xFF");
    }

    #[test]
    fn test_as_str() {
        let c_str = "hello".to_c_str();
        assert_eq!(c_str.as_str(), Some("hello"));
        let c_str = "".to_c_str();
        assert_eq!(c_str.as_str(), Some(""));
        let c_str = b"foo\xFF".to_c_str();
        assert_eq!(c_str.as_str(), None);
    }

    #[test]
    fn test_to_string() {
        let c_buf = c_buf_from_bytes(b"hello");;
        assert_eq!(c_buf.to_string(), Some(String::from_str("hello")));
        let c_buf = c_buf_from_bytes(b"");
        assert_eq!(c_buf.to_string(), Some(String::from_str("")));
        let c_buf = c_buf_from_bytes(b"foo\xFF");
        assert_eq!(c_buf.to_string(), None);
    }

    #[test]
    #[should_fail]
    fn test_buf_new_fail() {
        let _c_str = unsafe { CStrBuf::new_unowned(ptr::null()) };
    }

    #[test]
    #[should_fail]
    fn test_str_new_fail() {
        let _c_str = unsafe { CString::new_unowned(ptr::null(), 1) };
    }

    #[test]
    fn test_into_c_str() {
        let buf = c_buf_from_bytes(b"hello");
        let c_str = buf.into_c_str();
        assert_eq!(c_str.as_bytes(), b"hello\0");
    }
}

#[cfg(test)]
mod bench {
    use test::Bencher;
    use libc;
    use std::iter::range;
    use std::ptr::RawPtr;
    use std::str::StrSlice;

    use super::ToCStr;

    #[inline]
    fn check(s: &str, c_str: *const libc::c_char) {
        let s_buf = s.as_ptr();
        for i in range(0, s.len()) {
            unsafe {
                assert_eq!(
                    *s_buf.offset(i as int) as libc::c_char,
                    *c_str.offset(i as int));
            }
        }
    }

    static S_SHORT: &'static str = "Mary";
    static S_MEDIUM: &'static str = "Mary had a little lamb";
    static S_LONG: &'static str = "\
        Mary had a little lamb, Little lamb
        Mary had a little lamb, Little lamb
        Mary had a little lamb, Little lamb
        Mary had a little lamb, Little lamb
        Mary had a little lamb, Little lamb
        Mary had a little lamb, Little lamb";

    fn bench_to_string(b: &mut Bencher, s: &str) {
        b.iter(|| {
            let c_str = s.to_c_str();
            check(s, c_str.as_ptr());
        })
    }

    #[bench]
    fn bench_to_c_str_short(b: &mut Bencher) {
        bench_to_string(b, S_SHORT)
    }

    #[bench]
    fn bench_to_c_str_medium(b: &mut Bencher) {
        bench_to_string(b, S_MEDIUM)
    }

    #[bench]
    fn bench_to_c_str_long(b: &mut Bencher) {
        bench_to_string(b, S_LONG)
    }

    fn bench_to_c_str_unchecked(b: &mut Bencher, s: &str) {
        b.iter(|| {
            let c_str = unsafe { s.to_c_str_unchecked() };
            check(s, c_str.as_ptr())
        })
    }

    #[bench]
    fn bench_to_c_str_unchecked_short(b: &mut Bencher) {
        bench_to_c_str_unchecked(b, S_SHORT)
    }

    #[bench]
    fn bench_to_c_str_unchecked_medium(b: &mut Bencher) {
        bench_to_c_str_unchecked(b, S_MEDIUM)
    }

    #[bench]
    fn bench_to_c_str_unchecked_long(b: &mut Bencher) {
        bench_to_c_str_unchecked(b, S_LONG)
    }

    fn bench_with_c_str(b: &mut Bencher, s: &str) {
        b.iter(|| {
            s.with_c_str(|c_str_buf| check(s, c_str_buf))
        })
    }

    #[bench]
    fn bench_with_c_str_short(b: &mut Bencher) {
        bench_with_c_str(b, S_SHORT)
    }

    #[bench]
    fn bench_with_c_str_medium(b: &mut Bencher) {
        bench_with_c_str(b, S_MEDIUM)
    }

    #[bench]
    fn bench_with_c_str_long(b: &mut Bencher) {
        bench_with_c_str(b, S_LONG)
    }

    fn bench_with_c_str_unchecked(b: &mut Bencher, s: &str) {
        b.iter(|| {
            unsafe {
                s.with_c_str_unchecked(|c_str_buf| check(s, c_str_buf))
            }
        })
    }

    #[bench]
    fn bench_with_c_str_unchecked_short(b: &mut Bencher) {
        bench_with_c_str_unchecked(b, S_SHORT)
    }

    #[bench]
    fn bench_with_c_str_unchecked_medium(b: &mut Bencher) {
        bench_with_c_str_unchecked(b, S_MEDIUM)
    }

    #[bench]
    fn bench_with_c_str_unchecked_long(b: &mut Bencher) {
        bench_with_c_str_unchecked(b, S_LONG)
    }
}
