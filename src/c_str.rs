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
//! Both `OwnedCString` and `CStrBuf` dereference to `CStr`, a token type
//! that asserts the C string requirements when passed or returned
//! by reference. `&CStr` can be used to encapsulate FFI functions under a
//! safe facade.
//!
//! An example of creating and using a C string would be:
//!
//! ```rust
//! #![allow(unstable)]
//!
//! extern crate c_string;
//! extern crate libc;
//!
//! use c_string::{CStr, CStrBuf};
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

#![feature(collections)]
#![feature(core)]
#![feature(io)]
#![feature(libc)]

extern crate libc;

use std::cmp::Ordering;
use std::error::{Error, FromError};
use std::fmt;
use std::hash;
use std::io::Error as IoError;
use std::io::ErrorKind::InvalidInput;
use std::marker;
use std::mem;
use std::ops::Deref;
use std::slice;
use std::str;

const NUL: u8 = 0;

/// Representation of an allocated C String.
///
/// This structure wraps a raw pointer to a null-terminated C string
/// and a destructor function to invoke when dropped.
pub struct OwnedCString {
    ptr: *const libc::c_char,
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
pub type DestroyFn = unsafe fn(*const libc::c_char);

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
pub unsafe fn libc_free(ptr: *const libc::c_char) {
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
    pub unsafe fn new(ptr: *const libc::c_char, dtor: DestroyFn) -> OwnedCString {
        assert!(!ptr.is_null());
        OwnedCString { ptr: ptr, dtor: dtor }
    }
}

impl fmt::Debug for OwnedCString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

/// Error information about a failed string conversion due to an interior NUL
/// in the source data.
#[derive(Copy, Debug)]
pub struct NulError {

    /// The offset at which the first NUL occurs.
    position: usize
}

impl NulError {
    pub fn nul_position(&self) -> usize { self.position }
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

impl FromError<NulError> for IoError {
    fn from_error(err: NulError) -> IoError {
        IoError::new(InvalidInput, "invalid data for C string: contains a NUL byte",
                     Some(format!("NUL at position {}", err.position)))
    }
}

/// A possible error value from the `CStrBuf::from_vec` function.
#[derive(Debug)]
pub struct IntoCStrError {
    cause: NulError,
    bytes: Vec<u8>
}

impl IntoCStrError {

    /// Access the `NulError` that is the cause of this error.
    pub fn nul_error(&self) -> NulError {
        self.cause
    }

    /// Consume this error, returning the bytes that were attempted to make
    /// a C string with.
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

impl Error for IntoCStrError {

    fn description(&self) -> &str {
        self.cause.description()
    }
}

impl fmt::Display for IntoCStrError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.cause)
    }
}

impl FromError<IntoCStrError> for IoError {
    fn from_error(err: IntoCStrError) -> IoError {
        FromError::from_error(err.nul_error())
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
#[derive(Clone)]
pub struct CStrBuf {
    data: CStrData
}

/// A type to denote null-terminated string data borrowed under a reference.
///
/// `CStr` is only used by reference, e.g. as a parameter in a safe function
/// proxying its FFI counterpart.
#[repr(packed)]
pub struct CStr {
    chars: [libc::c_char]
}

fn bytes_into_c_str(s: &[u8]) -> CStrBuf {
    let mut out = CStrBuf {
        data: unsafe { blank_str_data() }
    };
    if !copy_in_place(s, &mut out.data) {
        out = vec_into_c_str(s.to_vec());
    }
    out
}

#[inline]
unsafe fn blank_str_data() -> CStrData {
    CStrData::InPlace(mem::uninitialized())
}

fn copy_in_place(s: &[u8], out: &mut CStrData) -> bool {
    let len = s.len();
    if len >= IN_PLACE_SIZE {
        return false;
    }
    match *out {
        CStrData::InPlace(ref mut buf) => {
            slice::bytes::copy_memory(buf, s);
            buf[len] = 0;
        }
        _ => unreachable!()
    }
    true
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
/// #![allow(unstable)]
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
        $crate::CStr::from_static_str(concat!($lit, "\0"))
    }
}

impl CStrBuf {

    /// Create a `CStrBuf` by copying a byte slice.
    ///
    /// # Failure
    ///
    /// Returns `Err` if the byte slice contains an interior NUL byte.
    pub fn from_bytes(s: &[u8]) -> Result<CStrBuf, NulError> {
        if let Some(pos) = s.position_elem(&NUL) {
            return Err(NulError { position: pos });
        }
        Ok(bytes_into_c_str(s))
    }

    /// Create a `CStrBuf` by copying a byte slice,
    /// without checking for interior NUL characters.
    pub unsafe fn from_bytes_unchecked(s: &[u8]) -> CStrBuf {
        bytes_into_c_str(s)
    }

    /// Create a `CStrBuf` by copying a string slice.
    ///
    /// # Failure
    ///
    /// Returns `Err` if the string contains an interior NUL character.
    #[inline]
    pub fn from_str(s: &str) -> Result<CStrBuf, NulError> {
        CStrBuf::from_bytes(s.as_bytes())
    }

    /// Create a `CStrBuf` by copying a string slice,
    /// without checking for interior NUL characters.
    #[inline]
    pub unsafe fn from_str_unchecked(s: &str) -> CStrBuf {
        CStrBuf::from_bytes_unchecked(s.as_bytes())
    }

    /// Consumes a byte vector to create `CStrBuf`, taking care to avoid
    /// copying.
    ///
    /// # Failure
    ///
    /// If the given vector contains a NUL byte, then an error containing
    /// the original vector and `NulError` information is returned.
    pub fn from_vec(vec: Vec<u8>) -> Result<CStrBuf, IntoCStrError> {
        if let Some(pos) = vec[..].position_elem(&NUL) {
            return Err(IntoCStrError {
                cause: NulError { position: pos },
                bytes: vec
            });
        }
        Ok(vec_into_c_str(vec))
    }

    /// Like `from_vec`, but without checking for interior NUL bytes.
    pub unsafe fn from_vec_unchecked(vec: Vec<u8>) -> CStrBuf {
        vec_into_c_str(vec)
    }

    /// Converts `self` into a byte vector, potentially saving an allocation.
    pub fn into_vec(mut self) -> Vec<u8> {
        let mut data = unsafe { blank_str_data() };
        mem::swap(&mut self.data, &mut data);
        match data {
            CStrData::Owned(mut v) => {
                let len = v.len() - 1;
                v.truncate(len);
                v
            }
            CStrData::InPlace(ref a) => {
                a[.. a.position_elem(&NUL).unwrap()].to_vec()
            }
        }
    }

    fn as_bytes(&self) -> &[u8] {
        match self.data {
            CStrData::Owned(ref v) => &v[.. v.len() - 1],
            CStrData::InPlace(ref a) => &a[.. a.position_elem(&NUL).unwrap()]
        }
    }
}

impl fmt::Debug for CStrBuf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\"{}\"", escape_bytestring(self.as_bytes()))
    }
}

impl CStr {

    /// Constructs a `CStr` reference from a raw pointer to a
    /// null-terminated string.
    ///
    /// This function is unsafe because there is no guarantee of the validity
    /// of the pointer `raw` or a guarantee that a NUL terminator will be found.
    /// Also there are no compile-time checks whether the lifetime as inferred
    /// is a suitable lifetime for the returned slice.
    ///
    /// # Caveat
    ///
    /// The lifetime of the returned reference is inferred from its usage.
    /// This may be incorrect in many cases. Consider this example:
    ///
    /// ```no_run
    /// #[macro_use]
    /// extern crate c_string;
    ///
    /// extern crate libc;
    /// extern "C" {
    ///     fn strdup(source: *const libc::c_char) -> *mut libc::c_char;
    /// }
    ///
    /// use c_string::CStr;
    ///
    /// fn main() {
    ///     let ptr = unsafe { strdup(c_str!("Hello!").as_ptr()) };
    ///
    ///     let s = unsafe { CStr::from_ptr(ptr).to_bytes() };
    ///
    ///     unsafe { libc::free(ptr as *mut libc::c_void) };
    ///
    ///     let guess_what = s[0];
    ///     // The lifetime of s is inferred to extend to the line above
    /// }
    /// ```
    ///
    /// To prevent accidental misuse, the lifetime should be restricted
    /// in some way. This can be a helper function or method taking the
    /// lifetime from a 'host' value, when available. In other cases, explicit
    /// annotation may be used.
    #[inline]
    pub unsafe fn from_ptr<'a>(raw: *const libc::c_char) -> &'a CStr {
        let inner = slice::from_raw_parts(raw, 1);
        mem::transmute(inner)
    }

    /// Create a `CStr` reference out of a static byte array.
    ///
    /// This function can be used with null-terminated byte string literals.
    /// For non-literal data, prefer `CStrBuf::from_bytes`, since that
    /// constructor checks for interior NUL bytes.
    ///
    /// # Panics
    ///
    /// Panics if the byte array is not null-terminated.
    pub fn from_static_bytes(bytes: &'static [u8]) -> &'static CStr {
        assert!(bytes.last() == Some(&NUL),
                "static byte string is not null-terminated: \"{}\"",
                escape_bytestring(bytes));
        let ptr = bytes.as_ptr() as *const libc::c_char;
        unsafe { CStr::from_ptr(ptr) }
    }

    /// Create a `CStr` reference out of a static string.
    ///
    /// This function can be used with null-terminated string literals.
    /// For non-literal data, prefer `CStrBuf::from_str`, since that
    /// constructor checks for interior NUL characters.
    ///
    /// # Panics
    ///
    /// Panics if the string is not null-terminated.
    pub fn from_static_str(s: &'static str) -> &'static CStr {
        assert!(s.ends_with("\0"),
                "static string is not null-terminated: \"{}\"", s);
        let ptr = s.as_ptr() as *const libc::c_char;
        unsafe { CStr::from_ptr(ptr) }
    }

    /// Returns a raw pointer to the null-terminated C string.
    ///
    /// The returned pointer can only be considered valid
    /// during the lifetime of the `CStr` value.
    #[inline]
    pub fn as_ptr(&self) -> *const libc::c_char {
        self.chars.as_ptr()
    }

    /// Scans the string to get a byte slice of its contents.
    ///
    /// The returned slice does not include the terminating NUL byte.
    pub fn to_bytes(&self) -> &[u8] {
        let ptr = self.as_ptr();
        unsafe {
            slice::from_raw_parts(ptr as *const u8, libc::strlen(ptr) as usize)
        }
    }

    /// Scans the string as UTF-8 string slice.
    ///
    /// # Failure
    ///
    /// Returns `Err` with information on the conversion error if the string is
    /// not valid UTF-8.
    #[inline]
    pub fn to_utf8(&self) -> Result<&str, str::Utf8Error> {
        str::from_utf8(self.to_bytes())
    }

    /// Returns an iterator over the string's bytes.
    #[inline]
    pub fn iter<'a>(&'a self) -> CChars<'a> {
        CChars {
            ptr: self.as_ptr(),
            lifetime: marker::PhantomData
        }
    }

    /// Returns true if the wrapped string is empty.
    #[inline]
    pub fn is_empty(&self) -> bool { self.chars[0] == 0 }
}

impl fmt::Debug for CStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\"{}\"", escape_bytestring(self.to_bytes()))
    }
}

impl Deref for CStrBuf {

    type Target = CStr;

    fn deref(&self) -> &CStr {
        let p = match self.data {
            CStrData::Owned(ref v)   => (*v).as_ptr(),
            CStrData::InPlace(ref a) => a.as_ptr()
        } as *const libc::c_char;
        unsafe { CStr::from_ptr(p) }
    }
}

/// External iterator for C string's bytes.
///
/// The iteration stops when the terminating NUL byte is reached, without
/// returning the NUL.
///
/// Use with the `std::iter` module.
#[derive(Copy)]
pub struct CChars<'a> {
    ptr: *const libc::c_char,
    lifetime: marker::PhantomData<&'a [libc::c_char]>,
}

impl<'a> Iterator for CChars<'a> {

    type Item = libc::c_char;

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
pub unsafe fn parse_c_multistring<F>(buf: *const libc::c_char,
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
