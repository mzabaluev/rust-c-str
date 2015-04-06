// Copyright 2014, 2015 Mikhail Zabaluev <mikhail.zabaluev@gmail.com>
// Copyright 2012 The Rust Project Developers
// See the COPYRIGHT file at the top-level directory of this distribution
// and at http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![crate_name = "c_string"]
#![crate_type = "lib"]

//! This library provides helpers for creating and managing
//! null-terminated strings for use with FFI calls. Most C APIs require
//! that the string being passed to them is null-terminated and many of them
//! allocate and return null-terminated strings, but Rust's built-in string
//! types are *not* null terminated.
//!
//! The other problem with translating Rust strings to C strings is that Rust
//! strings can validly contain a NUL byte in the middle of the string (0 is a
//! valid Unicode codepoint). This means that not all Rust strings can actually
//! be translated to C strings.
//!
//! # Managing foreign-allocated C strings
//!
//! An allocated C string is managed through the type `OwnedCString`.
//! Values of this type "own" an internal buffer of characters and will call
//! a destructor when the value is dropped.
//!
//! # Creation of a C string
//!
//! The type `CStrBuf` is used to adapt string data from Rust for calling
//! C functions that expect a null-terminated string. The conversion
//! constructors of `CStrBuf` provide various ways to produce C strings,
//! but the conversions can fail due to some of the limitations explained
//! above.
//!
//! # Borrowed C strings
//!
//! Both `OwnedCString` and `CStrBuf` dereference to `std::ffi::CStr`, an
//! unsized type that asserts the C string requirements when passed or
//! returned by reference. `&CStr` can be used to encapsulate FFI functions
//! under a safe facade.
//!
//! An example of creating and using a C string would be:
//!
//! ```rust
//!
//! extern crate c_string;
//! extern crate libc;
//!
//! use c_string::CStrBuf;
//! use std::ffi::CStr;
//!
//! fn safe_puts(s: &CStr) {
//!     unsafe { libc::puts(s.as_ptr()) };
//! }
//!
//! fn main() {
//!     let my_string = "Hello, world!";
//!
//!     // Allocate the C string with an explicit local that owns the string.
//!     // The string will be deallocated when `my_c_string` goes out of scope.
//!     let my_c_string = match CStrBuf::from_str(my_string) {
//!             Ok(s) => s,
//!             Err(e) => panic!(e)
//!         };
//!
//!     safe_puts(&my_c_string);
//! }
//! ```

#![allow(trivial_numeric_casts)]

extern crate libc;

use std::cmp::Ordering;
use std::error::Error;
use std::ffi::CStr;
use std::fmt;
use std::fmt::Debug;
use std::hash;
use std::io::Error as IoError;
use std::io::ErrorKind::InvalidInput;
use std::iter::IntoIterator;
use std::marker;
use std::mem;
use std::ops::Deref;

pub use libc::c_char;

const NUL: u8 = 0;

/// Representation of an allocated C String.
///
/// This structure wraps a raw pointer to a null-terminated C string
/// and a destructor function to invoke when dropped.
pub struct OwnedCString {
    ptr: *const c_char,
    dtor: DestroyFn
}

impl Drop for OwnedCString {
    fn drop(&mut self) {
        let dtor = self.dtor;
        unsafe { dtor(self.ptr) };
    }
}

impl Deref for OwnedCString {

    type Target = CStr;

    fn deref(&self) -> &CStr {
        unsafe { CStr::from_ptr(self.ptr) }
    }
}

impl PartialEq for OwnedCString {
    fn eq(&self, other: &OwnedCString) -> bool {
        unsafe { libc::strcmp(self.ptr, other.ptr) == 0 }
    }
}

impl Eq for OwnedCString {
}

impl PartialOrd for OwnedCString {
    #[inline]
    fn partial_cmp(&self, other: &OwnedCString) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OwnedCString {
    fn cmp(&self, other: &OwnedCString) -> Ordering {
        let res = unsafe { libc::strcmp(self.ptr, other.ptr) };
        res.cmp(&(0 as libc::c_int))
    }
}

impl hash::Hash for OwnedCString {
    fn hash<H>(&self, state: &mut H) where H: hash::Hasher {
        self.to_bytes().hash(state)
    }
}

/// Signature for deallocation functions used with `OwnedCString::new`.
pub type DestroyFn = unsafe fn(*const c_char);

/// The deallocation function that delegates to `libc::free`.
///
/// Use with `OwnedCString::new` for strings allocated with the standard C
/// allocation function linked as `libc::malloc`.
///
/// # Caution
///
/// On some platforms, such as Windows, the standard C allocator used by
/// non-Rust libraries is not necessarily the same as the one linked
/// with the crate `libc`.
pub unsafe fn libc_free(ptr: *const c_char) {
    libc::free(ptr as *mut libc::c_void);
}

impl OwnedCString {

    /// Create an `OwnedCString` from a raw pointer and a destructor.
    ///
    /// The destructor will be invoked when the `OwnedCString` is dropped.
    ///
    ///# Panics
    ///
    /// Panics if `ptr` is null.
    pub unsafe fn new(ptr: *const c_char, dtor: DestroyFn) -> OwnedCString {
        assert!(!ptr.is_null());
        OwnedCString { ptr: ptr, dtor: dtor }
    }
}

impl Debug for OwnedCString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\"{}\"", escape_bytestring(self.to_bytes()))
    }
}

/// Error information about a failed string conversion due to an interior NUL
/// in the source data.
pub struct NulError {
    position: usize,
    bytes: Vec<u8>
}

impl NulError {

    /// Returns the position of the first NUL byte in the byte sequence that
    /// was attempted to convert to `CStrBuf`.
    pub fn nul_position(&self) -> usize { self.position }

    /// Consumes this error and returns the bytes that were attempted to make
    /// a C string with.
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

impl Error for NulError {

    fn description(&self) -> &str {
        "invalid data for C string: contains a NUL byte"
    }
}

impl fmt::Display for NulError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "invalid data for C string: NUL at position {}", self.position)
    }
}

impl fmt::Debug for NulError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO: truncate output if too long
        write!(f, "NulError {{ position: {}, bytes: \"{}\" }}",
               self.position, escape_bytestring(&self.bytes))
    }
}

impl From<NulError> for IoError {
    fn from(err: NulError) -> IoError {
        IoError::new(InvalidInput,
            format!("invalid data for C string: NUL at position {}", err.position).as_ref())
    }
}

const IN_PLACE_SIZE: usize = 31;

#[derive(Clone)]
enum CStrData {
    Owned(Vec<u8>),
    InPlace([u8; IN_PLACE_SIZE])
}

/// An adaptor type to pass C string data to foreign functions.
///
/// Values of this type can be obtained by conversion from Rust strings and
/// byte slices.
///
/// This type serves the same purpose as `std::ffi::CString`, but provides
/// in-place optimization for small strings and different ergonomics in the
/// ways `CStrBuf` values can be constructed.
#[derive(Clone)]
pub struct CStrBuf {
    data: CStrData
}

fn find_nul(bytes: &[u8]) -> Option<usize> {
    bytes.iter().position(|b| *b == NUL)
}

fn vec_into_c_str(mut v: Vec<u8>) -> CStrBuf {
    v.push(NUL);
    CStrBuf { data: CStrData::Owned(v) }
}

fn escape_bytestring(s: &[u8]) -> String {
    use std::ascii;

    let mut acc = Vec::with_capacity(s.len());
    acc.extend(s.iter().cloned().flat_map(ascii::escape_default));
    unsafe { String::from_utf8_unchecked(acc) }
}

/// Produce a `CStr` reference out of a static string literal.
///
/// This macro provides a convenient way to use string literals in
/// expressions where a `CStr` reference is expected.
/// The macro parameter does not need to end with `"\0"`, it is
/// appended by the macro.
///
/// # Example
///
/// ```rust
///
/// #[macro_use]
/// extern crate c_string;
///
/// extern crate libc;
///
/// fn main() {
///     unsafe { libc::puts(c_str!("Hello, world!").as_ptr()) };
/// }
/// ```
#[macro_export]
macro_rules! c_str {
    ($lit:expr) => {
        // Currently, there is no working way to concatenate a byte string
        // literal out of bytestring or string literals. Otherwise, we could
        // use from_static_bytes and accept byte strings as well.
        // See https://github.com/rust-lang/rfcs/pull/566
        unsafe {
            std::ffi::CStr::from_ptr(concat!($lit, "\0").as_ptr()
                                        as *const $crate::c_char)
        }
    }
}

impl CStrBuf {

    /// Create a `CStrBuf` by consuming an iterable source of bytes.
    ///
    /// # Failure
    ///
    /// Returns `Err` if the source contains an interior NUL byte.
    pub fn from_iter<I>(iterable: I) -> Result<CStrBuf, NulError>
        where I: IntoIterator<Item=u8>
    {
        fn nul_error<I>(mut collected: Vec<u8>, remaining: I) -> NulError
            where I: Iterator<Item=u8>
        {
            let pos = collected.len();
            collected.push(NUL);
            collected.extend(remaining);
            NulError { position: pos, bytes: collected }
        }

        let mut iter = iterable.into_iter();
        let mut vec: Vec<u8> = match iter.size_hint() {
            (_, Some(len)) if len < IN_PLACE_SIZE => {
                // The iterator promises the items will fit into the
                // in-place variant.
                let mut buf: [u8; IN_PLACE_SIZE]
                           = unsafe { mem::uninitialized() };
                for i in 0 .. len + 1 {
                    match iter.next() {
                        Some(NUL) => {
                            return Err(nul_error(buf[.. i].to_vec(), iter));
                        }
                        Some(c) => {
                            buf[i] = c;
                        }
                        None => {
                            buf[i] = NUL;
                            return Ok(CStrBuf {
                                    data: CStrData::InPlace(buf)
                                });
                        }
                    }
                }
                // The upper bound on iterator length was a lie.
                // Copy the collected buffer into the vector
                // that the owned collection path will continue with
                let mut vec = Vec::<u8>::with_capacity(len + 2);
                vec.extend(buf[.. len + 1].iter().cloned());
                vec
            }
            (lower, _) => {
                Vec::with_capacity(lower + 1)
            }
        };
        // Loop invariant: vec.len() < vec.capacity()
        loop {
            match iter.next() {
                None => {
                    break;
                }
                Some(NUL) => {
                    return Err(nul_error(vec, iter));
                }
                Some(c) => {
                    let len = vec.len();
                    unsafe {
                        *vec.get_unchecked_mut(len) = c;
                        vec.set_len(len + 1);
                    }
                    if vec.len() == vec.capacity() {
                        // Get capacity for some more iterations and continue
                        let (lower, _) = iter.size_hint();
                        vec.reserve(lower + 1);
                    }
                }
            }
        }
        {
            let len = vec.len();
            unsafe {
                *vec.get_unchecked_mut(len) = NUL;
                vec.set_len(len + 1);
            }
        }
        Ok(CStrBuf { data: CStrData::Owned(vec) })
    }

    /// Create a `CStrBuf` by copying a string slice.
    ///
    /// # Failure
    ///
    /// Returns `Err` if the string contains an interior NUL character.
    #[inline]
    pub fn from_str(s: &str) -> Result<CStrBuf, NulError> {
        CStrBuf::from_iter(s.as_bytes().iter().cloned())
    }

    /// Consumes a byte vector to create `CStrBuf`, taking care to avoid
    /// copying.
    ///
    /// # Failure
    ///
    /// If the given vector contains a NUL byte, then an error containing
    /// the original vector and `NulError` information is returned.
    pub fn from_vec(vec: Vec<u8>) -> Result<CStrBuf, NulError> {
        if let Some(pos) = find_nul(&vec[..]) {
            return Err(NulError {position: pos, bytes: vec});
        }
        Ok(vec_into_c_str(vec))
    }

    /// Like `from_vec`, but without checking for interior NUL bytes.
    pub unsafe fn from_vec_unchecked(vec: Vec<u8>) -> CStrBuf {
        vec_into_c_str(vec)
    }

    /// Converts `self` into a byte vector, potentially saving an allocation.
    pub fn into_vec(mut self) -> Vec<u8> {
        match mem::replace(&mut self.data,
                           CStrData::InPlace(unsafe { mem::uninitialized() }))
        {
            CStrData::Owned(mut v) => {
                let len = v.len();
                v.truncate(len - 1);
                v
            }
            CStrData::InPlace(ref a) => {
                a[.. find_nul(a).unwrap()].to_vec()
            }
        }
    }

    fn as_bytes(&self) -> &[u8] {
        match self.data {
            CStrData::Owned(ref v) => &v[.. v.len() - 1],
            CStrData::InPlace(ref a) => &a[.. find_nul(a).unwrap()]
        }
    }
}

impl fmt::Debug for CStrBuf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\"{}\"", escape_bytestring(self.as_bytes()))
    }
}

impl Deref for CStrBuf {

    type Target = CStr;

    fn deref(&self) -> &CStr {
        let p = match self.data {
            CStrData::Owned(ref v)   => (*v).as_ptr(),
            CStrData::InPlace(ref a) => a.as_ptr()
        } as *const c_char;
        unsafe { CStr::from_ptr(p) }
    }
}

/// External iterator for C string's bytes.
///
/// The iteration stops when the terminating NUL byte is reached, without
/// returning the NUL.
///
/// Use with the `std::iter` module.
pub struct CChars<'a> {
    ptr: *const c_char,
    lifetime: marker::PhantomData<&'a [c_char]>,
}

impl<'a> CChars<'a> {
    #[inline]
    pub fn from_c_str(s: &'a CStr) -> CChars<'a> {
        CChars { ptr: s.as_ptr(), lifetime: marker::PhantomData }
    }
}

impl<'a> Clone for CChars<'a> {
    #[inline]
    fn clone(&self) -> CChars<'a> {
        CChars { ptr: self.ptr, lifetime: marker::PhantomData }
    }
}

impl<'a> Copy for CChars<'a> { }

impl<'a> Iterator for CChars<'a> {

    type Item = c_char;

    fn next(&mut self) -> Option<c_char> {
        let ch = unsafe { *self.ptr };
        if ch == 0 {
            None
        } else {
            self.ptr = unsafe { self.ptr.offset(1) };
            Some(ch)
        }
    }
}

/// Parses a C "multistring".
///
/// This function can be used to process the "multistring" format
/// used by some C APIs, e.g. Windows environment variable values or
/// the `req->ptr` result in a `uv_fs_readdir()` call.
///
/// Optionally, a `limit` can be passed in, limiting the
/// parsing to only being done `limit` times.
///
/// The specified closure is invoked with each string that
/// is found, and the number of strings found is returned.
pub unsafe fn parse_c_multistring<F>(buf: *const c_char,
                                     limit: Option<usize>,
                                     mut f: F) -> usize
    where F: FnMut(&[u8])
{
    let mut curr_ptr = buf;
    let mut ctr: usize = 0;
    let (limited_count, limit) = match limit {
        Some(limit) => (true, limit),
        None => (false, 0)
    };
    while (!limited_count || ctr < limit) && *curr_ptr != 0 {
        let bytes = CStr::from_ptr(curr_ptr).to_bytes();
        f(bytes);
        curr_ptr = curr_ptr.offset(bytes.len() as isize + 1);
        ctr += 1;
    }
    return ctr;
}
