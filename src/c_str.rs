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

//! C-string manipulation and management
//!
//! This modules provides the basic methods for creating and managing
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
//! # Creation of a C string
//!
//! An allocated C string is managed through the generic type `CString`
//! defined in this module. Values of this type "own" an internal buffer of
//! characters and will call a destructor when the value is dropped.
//!
//! The type `CStrIn` is used to adapt string data from Rust for calling
//! C functions that expect a null-terminated string. The conversion
//! constructors of `CStrIn` and implementations of trait `IntoCStr` provide
//! various ways to produce C strings, but the conversions can fail due to
//! some of the limitations explained above.
//!
//! An example of creating and using a C string would be:
//!
//! ```rust
//! extern crate c_compat;
//! extern crate libc;
//!
//! use c_compat::c_str::CStrIn;
//!
//! extern {
//!     fn puts(s: *const libc::c_char);
//! }
//!
//! fn main() {
//!     let my_string = "Hello, world!";
//!
//!     // Allocate the C string with an explicit local that owns the string. The
//!     // string will be deallocated when `my_c_string` goes out of scope.
//!     let my_c_string = CStrIn::from_str(my_string).unwrap();
//!     unsafe {
//!         puts(my_c_string.as_ptr());
//!     }
//! }
//! ```

#![no_implicit_prelude]

use std::default::Default;
use std::fmt;
use std::hash;
use std::kinds::marker;
use std::mem;
use std::prelude::{AsSlice, CloneSliceExt, Drop, Eq, FnMut, Iterator};
use std::prelude::{None, Option, Ord, Ordering, PartialEq, PartialEqSliceExt};
use std::prelude::{PartialOrd, RawPtr, Result, SliceExt, Some, StrExt, Vec};
use std::slice;
use std::str;
use std::string::String;
use libc;

const NUL: u8 = 0;

/// Scans a C string as a byte slice.
///
/// The returned slice does not include the terminating NUL byte.
///
/// # Panics
///
/// Panics if the string pointer is null.
pub unsafe fn parse_as_bytes(raw: & *const libc::c_char) -> &[u8] {
    assert!(raw.is_not_null());
    let r = mem::copy_lifetime(raw, &(*raw as *const u8));
    slice::from_raw_buf(r, libc::strlen(*raw) as uint)
}

/// Scans a C string as UTF-8 string slice.
///
/// # Failure
///
/// Returns `Err` if the string is not UTF-8.
///
/// # Panics
///
/// Panics if the string pointer is null.
#[inline]
pub unsafe fn parse_as_utf8<'a>(raw: & *const libc::c_char)
                               -> Result<&str, str::Utf8Error>
{
    str::from_utf8(parse_as_bytes(raw))
}

/// Scans a C string as UTF-8 string slice without validity checks.
///
/// # Panics
///
/// Panics if the string pointer is null.
#[inline]
pub unsafe fn parse_as_utf8_unchecked(raw: & *const libc::c_char)
                                     -> &str
{
    str::from_utf8_unchecked(parse_as_bytes(raw))
}

/// Representation of an allocated C String.
///
/// This structure wraps a raw pointer to a null-terminated C string
/// and a destructor to invoke when dropped.
pub struct CString<D> where D: Dtor {
    ptr: *const libc::c_char,
    dtor: D
}

#[unsafe_destructor]
impl<D> Drop for CString<D> where D: Dtor {
    fn drop(&mut self) {
        self.dtor.destroy(self.ptr);
    }
}

impl<D1, D2> PartialEq<CString<D2>> for CString<D1>
    where D1: Dtor, D2: Dtor
{
    fn eq(&self, other: &CString<D2>) -> bool {
        unsafe { libc::strcmp(self.ptr, other.ptr) == 0 }
    }
}

impl<D1, D2> Eq<CString<D2>> for CString<D1>
    where D1: Dtor, D2: Dtor
{
}

impl<D1, D2> PartialOrd<CString<D2>> for CString<D1>
    where D1: Dtor, D2: Dtor
{
    #[inline]
    fn partial_cmp(&self, other: &CString<D2>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<D1, D2> Ord<CString<D2>> for CString<D1>
    where D1: Dtor, D2: Dtor
{
    fn cmp(&self, other: &CString<D2>) -> Ordering {
        let res = unsafe { libc::strcmp(self.ptr, other.ptr) as int };
        res.cmp(&0)
    }
}

impl<S, D> hash::Hash<S> for CString<D>
    where S: hash::Writer, D: Dtor
{
    fn hash(&self, state: &mut S) {
        state.write(self.parse_as_bytes());
    }
}

/// The destructor trait for `CString`.
pub trait Dtor {
    /// Deallocates the string data.
    fn destroy(&mut self, data: *const libc::c_char);
}

/// A destructor for `CString` that uses `libc::free`
/// to deallocate the string.
#[deriving(Copy, Default)]
pub struct LibcDtor;

impl Dtor for LibcDtor {
    fn destroy(&mut self, data: *const libc::c_char) {
        unsafe { libc::free(data as *mut libc::c_void); }
    }
}

impl<D> CString<D> where D: Dtor + Default {

    /// Create a `CString` from a pointer.
    ///
    /// The returned `CString` will be deallocated with a default instance
    /// of the destructor type when the `CString` is dropped.
    ///
    ///# Panics
    ///
    /// Panics if `ptr` is null.
    pub unsafe fn from_raw_buf(ptr: *const libc::c_char) -> CString<D> {
        assert!(ptr.is_not_null());
        CString { ptr: ptr, dtor: Default::default() }
    }
}

impl<D> CString<D> where D: Dtor {

    /// Create a `CString` from a foreign pointer and a destructor.
    ///
    ///# Panics
    ///
    /// Panics if `ptr` is null.
    pub unsafe fn with_dtor(ptr: *mut libc::c_char, dtor: D) -> CString<D> {
        assert!(ptr.is_not_null());
        CString { ptr: ptr, dtor: dtor }
    }

    /// Scans the string to get a byte slice of its contents.
    ///
    /// The returned slice does not include the terminating NUL byte.
    pub fn parse_as_bytes(&self) -> &[u8] {
        unsafe {
            let r = mem::copy_lifetime(self, &(self.ptr as *const u8));
            slice::from_raw_buf(r, libc::strlen(self.ptr) as uint)
        }
    }

    /// Scans the string as UTF-8 string slice.
    ///
    /// # Failure
    ///
    /// Returns `Err` if the string is not UTF-8.
    #[inline]
    pub fn parse_as_utf8<'a>(&self) -> Result<&str, str::Utf8Error> {
        str::from_utf8(self.parse_as_bytes())
    }

    /// Scans the string as UTF-8 string slice without validity checks.
    #[inline]
    pub unsafe fn parse_as_utf8_unchecked<'a>(&'a self) -> &'a str {
        str::from_utf8_unchecked(self.parse_as_bytes())
    }

    /// Return a raw pointer to the null-terminated string data.
    ///
    /// `.as_ptr` returns an internal pointer into the `CString`, and
    /// may be invalidated when the `CString` falls out of scope (the
    /// destructor will run, freeing the allocation if there is
    /// one).
    pub fn as_ptr(&self) -> *const libc::c_char {
        self.ptr
    }

    /// Returns an iterator over the string's bytes.
    pub fn iter<'a>(&'a self) -> CChars<'a> {
        CChars {
            ptr: self.ptr,
            lifetime: marker::ContravariantLifetime,
        }
    }

    /// Returns true if the wrapped string is empty.
    pub fn is_empty(&self) -> bool { unsafe { *self.ptr == 0 } }
}

impl<D> fmt::Show for CString<D> where D: Dtor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        String::from_utf8_lossy(self.parse_as_bytes()).fmt(f)
    }
}

enum CStrData {
    Static(&'static [u8]),
    Owned(Vec<u8>)
}

/// An adaptor type to pass C string data to foreign functions.
///
/// Values of this type can be obtained by conversion from Rust strings and
/// byte slices.
pub struct CStrIn {
    data: CStrData
}

fn vec_into_c_str(mut v: Vec<u8>) -> CStrIn {
    v.push(NUL);
    CStrIn { data: CStrData::Owned(v) }
}

impl CStrIn {

    /// Create a `CStrIn` by copying a byte slice.
    ///
    /// If the byte slice contains an interior NUL byte, `None` is returned.
    pub fn from_bytes(s: &[u8]) -> Option<CStrIn> {
        if s.contains(&NUL) {
            return None;
        }
        Some(vec_into_c_str(s.to_vec()))
    }

    /// Create a `CStrIn` by copying a byte slice,
    /// without checking for interior NUL characters.
    pub unsafe fn from_bytes_unchecked(s: &[u8]) -> CStrIn {
        vec_into_c_str(s.to_vec())
    }

    /// Create a `CStrIn` by copying a string slice.
    ///
    /// If the string contains an interior NUL character, `None` is returned.
    #[inline]
    pub fn from_str(s: &str) -> Option<CStrIn> {
        CStrIn::from_bytes(s.as_bytes())
    }

    /// Create a `CStrIn` by copying a string slice,
    /// without checking for interior NUL characters.
    #[inline]
    pub unsafe fn from_str_unchecked(s: &str) -> CStrIn {
        CStrIn::from_bytes_unchecked(s.as_bytes())
    }

    /// Create a `CStrIn` wrapping a static byte array.
    ///
    /// This constructor can be used with null-terminated byte string literals.
    /// For non-literal data, prefer `from_bytes`, since that constructor
    /// checks for interior NUL bytes.
    ///
    /// # Panics
    ///
    /// Panics if the byte array is not null-terminated.
    pub fn from_static_bytes(bytes: &'static [u8]) -> CStrIn {
        assert!(bytes[bytes.len() - 1] == NUL,
                "static byte string is not null-terminated: \"{}\"", bytes);
        CStrIn { data: CStrData::Static(bytes) }
    }

    /// Create a `CStrIn` wrapping a static string.
    ///
    /// This constructor can be used with null-terminated string literals.
    /// For non-literal data, prefer `from_str`, since that constructor
    /// checks for interior NUL characters.
    ///
    /// # Panics
    ///
    /// Panics if the string is not null-terminated.
    pub fn from_static_str(s: &'static str) -> CStrIn {
        let bytes = s.as_bytes();
        assert!(bytes[bytes.len() - 1] == NUL,
                "static string is not null-terminated: \"{}\"", s);
        CStrIn { data: CStrData::Static(bytes) }
    }

    /// Returns a raw pointer to the null-terminated C string.
    ///
    /// The returned pointer is internal to the `CStrIn` value,
    /// therefore it is invalidated when the value is dropped.
    pub fn as_ptr(&self) -> *const libc::c_char {
        match self.data {
            CStrData::Static(s)     => s.as_ptr() as *const libc::c_char,
            CStrData::Owned(ref v)  => v.as_ptr() as *const libc::c_char
        }
    }
}

/// A generic trait for transforming data into C string in-parameter values.
///
/// Depending on the implementation, the conversion may avoid allocation
/// and copying of the string buffer.
pub trait IntoCStr {

    /// Transform the receiver into a `CStrIn`.
    ///
    /// If the receiver contains interior null bytes, `None` is returned.
    fn into_c_str(self) -> Option<CStrIn>;

    /// Transform the receiver into a `CStrIn`
    /// without checking for interior NUL bytes.
    unsafe fn into_c_str_unchecked(self) -> CStrIn;
}

impl<'a> IntoCStr for &'a [u8] {

    #[inline]
    fn into_c_str(self) -> Option<CStrIn> {
        CStrIn::from_bytes(self)
    }

    #[inline]
    unsafe fn into_c_str_unchecked(self) -> CStrIn {
        CStrIn::from_bytes_unchecked(self)
    }
}

impl<'a> IntoCStr for &'a str {

    #[inline]
    fn into_c_str(self) -> Option<CStrIn> {
        CStrIn::from_str(self)
    }

    #[inline]
    unsafe fn into_c_str_unchecked(self) -> CStrIn {
        CStrIn::from_str_unchecked(self)
    }
}

impl IntoCStr for Vec<u8> {

    fn into_c_str(self) -> Option<CStrIn> {
        if self.as_slice().contains(&NUL) {
            return None;
        }
        Some(vec_into_c_str(self))
    }

    unsafe fn into_c_str_unchecked(self) -> CStrIn {
        vec_into_c_str(self)
    }
}

impl IntoCStr for String {

    #[inline]
    fn into_c_str(self) -> Option<CStrIn> {
        self.into_bytes().into_c_str()
    }

    #[inline]
    unsafe fn into_c_str_unchecked(self) -> CStrIn {
        self.into_bytes().into_c_str_unchecked()
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
    lifetime: marker::ContravariantLifetime<'a>,
}

impl<'a> CChars<'a> {

    /// Constructs a `CChars` iterator from a raw pointer to a
    /// null-terminated string.
    ///
    /// # Panics
    ///
    /// Panics if the pointer is null.
    pub unsafe fn from_raw_ptr(ptr: &'a *const libc::c_char) -> CChars<'a> {
        assert!(ptr.is_not_null());
        CChars { ptr: *ptr, lifetime: marker::ContravariantLifetime }
    }
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
/// the `req->ptr` result in a `uv_fs_readdir()` call.
///
/// Optionally, a `limit` can be passed in, limiting the
/// parsing to only being done `limit` times.
///
/// The specified closure is invoked with each string that
/// is found, and the number of strings found is returned.
pub unsafe fn from_c_multistring<F>(buf: *const libc::c_char,
                                    limit: Option<uint>,
                                    mut f: F) -> uint
    where F: FnMut(&[u8])
{
    let mut curr_ptr = buf;
    let mut ctr = 0u;
    let (limited_count, limit) = match limit {
        Some(limit) => (true, limit),
        None => (false, 0)
    };
    while (!limited_count || ctr < limit) && *curr_ptr != 0 {
        let len = libc::strlen(curr_ptr) as uint;
        f(slice::from_raw_buf(&(curr_ptr as *const u8), len));
        curr_ptr = curr_ptr.offset(len as int + 1);
        ctr += 1;
    }
    return ctr;
}

#[cfg(test)]
mod testutil {
    use super::CStrIn;
    use std::prelude::{RawPtr,SliceExt};
    use std::iter::range;

    #[inline]
    pub fn check_c_str(c_str: &CStrIn, expected: &[u8]) {
        let buf = c_str.as_ptr();
        let len = expected.len();
        for i in range(0u, len) {
            let byte = unsafe { *buf.offset(i as int) as u8 };
            assert_eq!(byte, expected[i]);
        }
        let term = unsafe { *buf.offset(len as int) as u8 };
        assert_eq!(term, 0);
    }
}

#[cfg(test)]
mod tests {
    use std::iter::Iterator;
    use std::prelude::{Clone, CloneSliceExt, None, Ok, RawPtr, SliceExt, Some};
    use std::prelude::{StrExt, String, Vec};
    use std::ptr;
    use libc;
    use super::testutil::check_c_str;

    use super::{CString,IntoCStr,CChars,LibcDtor};
    use super::from_c_multistring;

    fn bytes_dup(s: &[u8]) -> CString<LibcDtor> {
        let len = s.len();
        unsafe {
            let dup = libc::malloc(len as libc::size_t) as *mut u8;
            ptr::copy_nonoverlapping_memory(dup, s.as_ptr(), len);
            *dup.offset(len as int) = 0;
            CString::from_raw_buf(dup as *const i8)
        }
    }

    fn str_dup(s: &str) -> CString<LibcDtor> {
        bytes_dup(s.as_bytes())
    }

    #[test]
    fn test_str_multistring_parsing() {
        unsafe {
            let input = b"zero\0one\0\0";
            let ptr = input.as_ptr();
            let expected = ["zero", "one"];
            let mut it = expected.iter();
            let result = from_c_multistring(ptr as *const libc::c_char, None,
                |cbytes| {
                    assert_eq!(cbytes, it.next().unwrap().as_bytes());
                });
            assert_eq!(result, 2);
            assert!(it.next().is_none());
        }
    }

    fn test_into_c_str<Src>(sources: Vec<Src>,
                            expected: &[&'static [u8]],
                            invalid: Src)
        where Src: IntoCStr + Clone
    {
        let mut i = 0;
        for src in sources.into_iter() {
            let c_str = src.clone().into_c_str().unwrap();
            check_c_str(&c_str, expected[i]);
            let c_str = unsafe { src.into_c_str_unchecked() };
            check_c_str(&c_str, expected[i]);
            i += 1;
        }

        assert!(invalid.into_c_str().is_none());
    }

    #[test]
    fn test_bytes_into_c_str() {
        test_into_c_str(vec!(b"", b"hello", b"foo\xFF"),
                        &[b"", b"hello", b"foo\xFF"],
                        b"he\x00llo");
    }

    #[test]
    fn test_vec_into_c_str() {
        test_into_c_str(vec!(b"".to_vec(), b"hello".to_vec(), b"foo\xFF".to_vec()),
                        &[b"", b"hello", b"foo\xFF"],
                        b"he\x00llo".to_vec());
    }

    #[test]
    fn test_str_into_c_str() {
        test_into_c_str(vec!("", "hello"),
                        &[b"", b"hello"],
                        "he\x00llo");
    }

    #[test]
    fn test_string_into_c_str() {
        test_into_c_str(vec!(String::from_str(""), String::from_str("hello")),
                        &[b"", b"hello"],
                        String::from_str("he\x00llo"));
    }

    #[test]
    fn test_as_ptr() {
        let c_str = str_dup("hello");
        let len = unsafe { libc::strlen(c_str.as_ptr()) };
        assert_eq!(len, 5);
    }

    #[test]
    fn test_iterator() {
        let c_str = str_dup("");
        let mut iter = c_str.iter();
        assert_eq!(iter.next(), None);

        let c_str = str_dup("hello");
        let mut iter = c_str.iter();
        assert_eq!(iter.next(), Some('h' as libc::c_char));
        assert_eq!(iter.next(), Some('e' as libc::c_char));
        assert_eq!(iter.next(), Some('l' as libc::c_char));
        assert_eq!(iter.next(), Some('l' as libc::c_char));
        assert_eq!(iter.next(), Some('o' as libc::c_char));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_parse_as_bytes() {
        let c_str = str_dup("hello");
        let bytes = unsafe { super::parse_as_bytes(&c_str.ptr) };
        assert_eq!(bytes, b"hello");
        let c_str = str_dup("");
        let bytes = unsafe { super::parse_as_bytes(&c_str.ptr) };
        assert_eq!(bytes, b"");
        let c_str = bytes_dup(b"foo\xFF");
        let bytes = unsafe { super::parse_as_bytes(&c_str.ptr) };
        assert_eq!(bytes, b"foo\xFF");
    }

    #[test]
    fn test_parse_as_utf8() {
        let c_str = str_dup("hello");
        let res = unsafe { super::parse_as_utf8(&c_str.ptr) };
        assert_eq!(res, Ok("hello"));
        let c_str = str_dup("");
        let res = unsafe { super::parse_as_utf8(&c_str.ptr) };
        assert_eq!(res, Ok(""));
        let c_str = bytes_dup(b"foo\xFF");
        let res = unsafe { super::parse_as_utf8(&c_str.ptr) };
        assert!(res.is_err());
    }

    #[test]
    fn test_parse_as_utf8_unchecked() {
        let c_str = str_dup("hello");
        let s = unsafe { super::parse_as_utf8_unchecked(&c_str.ptr) };
        assert_eq!(s, "hello");
        let c_str = str_dup("");
        let s = unsafe { super::parse_as_utf8_unchecked(&c_str.ptr) };
        assert_eq!(s, "");
    }

    #[test]
    fn test_c_str_parse_as_bytes() {
        let c_str = str_dup("hello");
        assert_eq!(c_str.parse_as_bytes(), b"hello");
        let c_str = str_dup("");
        assert_eq!(c_str.parse_as_bytes(), b"");
        let c_str = bytes_dup(b"foo\xFF");
        assert_eq!(c_str.parse_as_bytes(), b"foo\xFF");
    }

    #[test]
    fn test_c_str_parse_as_utf8() {
        let c_str = str_dup("hello");
        assert_eq!(c_str.parse_as_utf8(), Ok("hello"));
        let c_str = str_dup("");
        assert_eq!(c_str.parse_as_utf8(), Ok(""));
        let c_str = bytes_dup(b"foo\xFF");
        assert!(c_str.parse_as_utf8().is_err());
    }

    #[test]
    fn test_c_str_parse_as_utf8_unchecked() {
        let c_str = str_dup("hello");
        let s = unsafe { c_str.parse_as_utf8_unchecked() };
        assert_eq!(s, "hello");
        let c_str = str_dup("");
        let s = unsafe { c_str.parse_as_utf8_unchecked() };
        assert_eq!(s, "");
    }

    #[test]
    #[should_fail]
    fn test_parse_null_as_bytes_fail() {
        unsafe {
            let p: *const libc::c_char = ptr::null();
            let _ = super::parse_as_bytes(&p);
        };
    }

    #[test]
    #[should_fail]
    fn test_parse_null_as_utf8_fail() {
        unsafe {
            let p: *const libc::c_char = ptr::null();
            let _ = super::parse_as_utf8(&p);
        };
    }

    #[test]
    #[should_fail]
    fn test_parse_null_as_utf8_unchecked_fail() {
        unsafe {
            let p: *const libc::c_char = ptr::null();
            let _ = super::parse_as_utf8_unchecked(&p);
        };
    }

    #[test]
    #[should_fail]
    fn test_str_constructor_fail() {
        let _c_str = unsafe { CString::from_raw_buf(ptr::null()) };
    }

    #[test]
    #[should_fail]
    fn test_chars_constructor_fail() {
        let p: *const libc::c_char = ptr::null();
        let _chars = unsafe { CChars::from_raw_ptr(&p) };
    }
}

#[cfg(test)]
mod bench {
    use test::Bencher;
    use std::prelude::{Str, StrExt, ToString};
    use super::testutil::check_c_str;

    use super::IntoCStr;

    #[inline]
    fn check_into_c_str<Src>(s: Src, expected: &str) where Src: IntoCStr {
        let c_str = s.into_c_str().unwrap();
        check_c_str(&c_str, expected.as_bytes());
    }

    #[inline]
    fn check_into_c_str_unchecked<Src>(s: Src, expected: &str) where Src: IntoCStr {
        let c_str = unsafe { s.into_c_str_unchecked() };
        check_c_str(&c_str, expected.as_bytes());
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

    // When benchmarking conversion from borrowed values, make a copy
    // for every iteration to equalize the work external to the
    // code under test.

    fn bench_str_into_c_str(b: &mut Bencher, s: &str) {
        b.iter(|| {
            check_into_c_str(s.to_string().as_slice(), s);
        })
    }

    #[bench]
    fn bench_str_into_c_str_short(b: &mut Bencher) {
        bench_str_into_c_str(b, S_SHORT)
    }

    #[bench]
    fn bench_str_into_c_str_medium(b: &mut Bencher) {
        bench_str_into_c_str(b, S_MEDIUM)
    }

    #[bench]
    fn bench_str_into_c_str_long(b: &mut Bencher) {
        bench_str_into_c_str(b, S_LONG)
    }

    fn bench_str_into_c_str_unchecked(b: &mut Bencher, s: &str) {
        b.iter(|| {
            check_into_c_str_unchecked(s.to_string().as_slice(), s);
        })
    }

    #[bench]
    fn bench_str_into_c_str_unchecked_short(b: &mut Bencher) {
        bench_str_into_c_str_unchecked(b, S_SHORT)
    }

    #[bench]
    fn bench_str_into_c_str_unchecked_medium(b: &mut Bencher) {
        bench_str_into_c_str_unchecked(b, S_MEDIUM)
    }

    #[bench]
    fn bench_str_into_c_str_unchecked_long(b: &mut Bencher) {
        bench_str_into_c_str_unchecked(b, S_LONG)
    }

    fn bench_string_into_c_str(b: &mut Bencher, s: &str) {
        b.iter(|| {
            check_into_c_str(s.to_string(), s);
        })
    }

    #[bench]
    fn bench_string_into_c_str_short(b: &mut Bencher) {
        bench_string_into_c_str(b, S_SHORT)
    }

    #[bench]
    fn bench_string_into_c_str_medium(b: &mut Bencher) {
        bench_string_into_c_str(b, S_MEDIUM)
    }

    #[bench]
    fn bench_string_into_c_str_long(b: &mut Bencher) {
        bench_string_into_c_str(b, S_LONG)
    }

    fn bench_string_into_c_str_unchecked(b: &mut Bencher, s: &str) {
        b.iter(|| {
            check_into_c_str_unchecked(s.to_string(), s);
        })
    }

    #[bench]
    fn bench_string_into_c_str_unchecked_short(b: &mut Bencher) {
        bench_string_into_c_str_unchecked(b, S_SHORT)
    }

    #[bench]
    fn bench_string_into_c_str_unchecked_medium(b: &mut Bencher) {
        bench_string_into_c_str_unchecked(b, S_MEDIUM)
    }

    #[bench]
    fn bench_string_into_c_str_unchecked_long(b: &mut Bencher) {
        bench_string_into_c_str_unchecked(b, S_LONG)
    }
}
