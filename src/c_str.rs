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
//! The type `CStrArg` is used to adapt string data from Rust for calling
//! C functions that expect a null-terminated string. The conversion
//! constructors of `CStrArg` and implementations of trait `IntoCStr` provide
//! various ways to produce C strings, but the conversions can fail due to
//! some of the limitations explained above.
//!
//! An example of creating and using a C string would be:
//!
//! ```rust
//! #![allow(unstable)]
//!
//! extern crate c_compat;
//! extern crate libc;
//!
//! use c_compat::c_str::CStrArg;
//!
//! extern {
//!     fn puts(s: *const libc::c_char);
//! }
//!
//! fn main() {
//!     let my_string = "Hello, world!";
//!
//!     // Allocate the C string with an explicit local that owns the string.
//!     // The string will be deallocated when `my_c_string` goes out of scope.
//!     let my_c_string = match CStrArg::from_str(my_string) {
//!             Ok(s) => s,
//!             Err(e) => panic!(e)
//!         };
//!     unsafe {
//!         puts(my_c_string.as_ptr());
//!     }
//! }
//! ```

use std::cmp::Ordering;
use std::default::Default;
use std::error::Error;
use std::fmt;
use std::hash;
use std::marker;
use std::mem;
use std::slice;
use libc;

const NUL: u8 = 0;

/// Scans a C string as a byte slice.
///
/// The returned slice does not include the terminating NUL byte.
///
/// # Panics
///
/// Panics if the string pointer is null.
pub unsafe fn parse_as_bytes<'a, T: ?Sized>(raw: *const libc::c_char,
                                            life_anchor: &'a T)
                                           -> &'a [u8]
{
    assert!(!raw.is_null());
    let r = mem::copy_lifetime(life_anchor, &(raw as *const u8));
    slice::from_raw_buf(r, libc::strlen(raw) as usize)
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

impl<D1> Eq for CString<D1>
    where D1: Dtor
{
}

impl<D1, D2> PartialOrd<CString<D2>> for CString<D1>
    where D1: Dtor, D2: Dtor
{
    fn partial_cmp(&self, other: &CString<D2>) -> Option<Ordering> {
        let res = unsafe { libc::strcmp(self.ptr, other.ptr) as i32 };
        res.partial_cmp(&0i32)
    }
}

impl<D1> Ord for CString<D1>
    where D1: Dtor
{
    fn cmp(&self, other: &Self) -> Ordering {
        let res = unsafe { libc::strcmp(self.ptr, other.ptr) as i32 };
        res.cmp(&0i32)
    }
}

impl<D, H> hash::Hash<H> for CString<D>
    where D: Dtor, H: hash::Hasher + hash::Writer
{
    fn hash(&self, state: &mut H) {
        self.parse_as_bytes().hash(state)
    }
}

/// The destructor trait for `CString`.
pub trait Dtor {
    /// Deallocates the string data.
    fn destroy(&mut self, data: *const libc::c_char);
}

/// A destructor for `CString` that uses `libc::free`
/// to deallocate the string.
#[derive(Copy, Default)]
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
        assert!(!ptr.is_null());
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
        assert!(!ptr.is_null());
        CString { ptr: ptr, dtor: dtor }
    }

    /// Scans the string to get a byte slice of its contents.
    ///
    /// The returned slice does not include the terminating NUL byte.
    pub fn parse_as_bytes(&self) -> &[u8] {
        unsafe {
            let r = mem::copy_lifetime(self, &(self.ptr as *const u8));
            slice::from_raw_buf(r, libc::strlen(self.ptr) as usize)
        }
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

/// Errors which can occur when attempting to convert data to a C string.
#[derive(Copy)]
pub enum CStrError {

    /// The source string or a byte sequence contains a NUL byte.
    ///
    /// The integer gives a byte offset where the first NUL occurs.
    ContainsNul(usize)
}

impl Error for CStrError {

    fn description(&self) -> &str {
        match *self {
            CStrError::ContainsNul(_)
                => "invalid data for C string: contains a NUL byte"
        }
    }

    fn detail(&self) -> Option<String> {
        match *self {
            CStrError::ContainsNul(pos)
                => Some(format!("NUL at position {}", pos))
        }
    }
}

impl fmt::Show for CStrError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            CStrError::ContainsNul(pos)
                => write!(f, "invalid data for C string: NUL at position {}", pos),
        }
    }
}

const IN_PLACE_LEN: usize = 15;

enum CStrData {
    Static(&'static [u8]),
    Owned(Vec<u8>),
    InPlace([u8; IN_PLACE_LEN + 1])
}

/// An adaptor type to pass C string data to foreign functions.
///
/// Values of this type can be obtained by conversion from Rust strings and
/// byte slices.
pub struct CStrArg {
    data: CStrData
}

fn bytes_into_c_str(s: &[u8]) -> CStrArg {
    copy_in_place(s).unwrap_or(long_vec_into_c_str(s.to_vec()))
}

fn vec_into_c_str(v: Vec<u8>) -> CStrArg {
    copy_in_place(v.as_slice()).unwrap_or(long_vec_into_c_str(v))
}

fn copy_in_place(s: &[u8]) -> Option<CStrArg> {
    let len = s.len();
    if len <= IN_PLACE_LEN {
        let mut buf: [u8; IN_PLACE_LEN + 1] = unsafe { mem::uninitialized() };
        slice::bytes::copy_memory(&mut buf, s);
        buf[len] = 0;
        return Some(CStrArg { data: CStrData::InPlace(buf) });
    }
    None
}

fn long_vec_into_c_str(mut v: Vec<u8>) -> CStrArg {
    v.push(NUL);
    CStrArg { data: CStrData::Owned(v) }
}

fn escape_bytestring(s: &[u8]) -> String {
    use std::ascii;

    let mut acc = Vec::with_capacity(s.len());
    for c in s.iter() {
        ascii::escape_default(*c, |esc| {
            acc.push(esc);
        })
    }
    unsafe { String::from_utf8_unchecked(acc) }
}

impl CStrArg {

    /// Create a `CStrArg` by copying a byte slice.
    ///
    /// # Failure
    ///
    /// Returns `Err` the byte slice contains an interior NUL byte.
    pub fn from_bytes(s: &[u8]) -> Result<CStrArg, CStrError> {
        if let Some(pos) = s.position_elem(&NUL) {
            return Err(CStrError::ContainsNul(pos));
        }
        Ok(bytes_into_c_str(s))
    }

    /// Create a `CStrArg` by copying a byte slice,
    /// without checking for interior NUL characters.
    pub unsafe fn from_bytes_unchecked(s: &[u8]) -> CStrArg {
        bytes_into_c_str(s)
    }

    /// Create a `CStrArg` by copying a string slice.
    ///
    /// # Failure
    ///
    /// Returns `Err` if the string contains an interior NUL character.
    #[inline]
    pub fn from_str(s: &str) -> Result<CStrArg, CStrError> {
        CStrArg::from_bytes(s.as_bytes())
    }

    /// Create a `CStrArg` by copying a string slice,
    /// without checking for interior NUL characters.
    #[inline]
    pub unsafe fn from_str_unchecked(s: &str) -> CStrArg {
        CStrArg::from_bytes_unchecked(s.as_bytes())
    }

    /// Create a `CStrArg` wrapping a static byte array.
    ///
    /// This constructor can be used with null-terminated byte string literals.
    /// For non-literal data, prefer `from_bytes`, since that constructor
    /// checks for interior NUL bytes.
    ///
    /// # Panics
    ///
    /// Panics if the byte array is not null-terminated.
    pub fn from_static_bytes(bytes: &'static [u8]) -> CStrArg {
        assert!(bytes.last() == Some(&NUL),
                "static byte string is not null-terminated: \"{}\"",
                escape_bytestring(bytes));
        CStrArg { data: CStrData::Static(bytes) }
    }

    /// Create a `CStrArg` wrapping a static string.
    ///
    /// This constructor can be used with null-terminated string literals.
    /// For non-literal data, prefer `from_str`, since that constructor
    /// checks for interior NUL characters.
    ///
    /// # Panics
    ///
    /// Panics if the string is not null-terminated.
    pub fn from_static_str(s: &'static str) -> CStrArg {
        assert!(s.ends_with("\0"),
                "static string is not null-terminated: \"{}\"", s);
        CStrArg { data: CStrData::Static(s.as_bytes()) }
    }

    /// Returns a raw pointer to the null-terminated C string.
    ///
    /// The returned pointer is internal to the `CStrArg` value,
    /// therefore it is invalidated when the value is dropped.
    pub fn as_ptr(&self) -> *const libc::c_char {
        match self.data {
            CStrData::Static(s)      => s.as_ptr() as *const libc::c_char,
            CStrData::Owned(ref v)   => v.as_ptr() as *const libc::c_char,
            CStrData::InPlace(ref a) => a.as_ptr() as *const libc::c_char
        }
    }
}

/// A generic trait for transforming data into C string in-parameter values.
///
/// Depending on the implementation, the conversion may avoid allocation
/// and copying of the string buffer.
pub trait IntoCStr {

    /// Transforms the receiver into a `CStrArg`.
    ///
    /// # Failure
    ///
    /// Returns `Err` if the receiver contains an interior NUL byte.
    fn into_c_str(self) -> Result<CStrArg, CStrError>;

    /// Transforms the receiver into a `CStrArg`
    /// without checking for interior NUL bytes.
    unsafe fn into_c_str_unchecked(self) -> CStrArg;
}

impl<'a> IntoCStr for &'a [u8] {

    #[inline]
    fn into_c_str(self) -> Result<CStrArg, CStrError> {
        CStrArg::from_bytes(self)
    }

    #[inline]
    unsafe fn into_c_str_unchecked(self) -> CStrArg {
        CStrArg::from_bytes_unchecked(self)
    }
}

impl<'a> IntoCStr for &'a str {

    #[inline]
    fn into_c_str(self) -> Result<CStrArg, CStrError> {
        CStrArg::from_str(self)
    }

    #[inline]
    unsafe fn into_c_str_unchecked(self) -> CStrArg {
        CStrArg::from_str_unchecked(self)
    }
}

impl IntoCStr for Vec<u8> {

    fn into_c_str(self) -> Result<CStrArg, CStrError> {
        if let Some(pos) = self.as_slice().position_elem(&NUL) {
            return Err(CStrError::ContainsNul(pos));
        }
        Ok(vec_into_c_str(self))
    }

    unsafe fn into_c_str_unchecked(self) -> CStrArg {
        vec_into_c_str(self)
    }
}

impl IntoCStr for String {

    #[inline]
    fn into_c_str(self) -> Result<CStrArg, CStrError> {
        self.into_bytes().into_c_str()
    }

    #[inline]
    unsafe fn into_c_str_unchecked(self) -> CStrArg {
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
    pub unsafe fn from_raw_ptr<T: ?Sized>(ptr: *const libc::c_char,
                                          _life_anchor: &'a T)
                                         -> CChars<'a>
    {
        assert!(!ptr.is_null());
        CChars { ptr: ptr, lifetime: marker::ContravariantLifetime }
    }
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

/// Parses a C "multistring", eg windows env values or
/// the `req->ptr` result in a `uv_fs_readdir()` call.
///
/// Optionally, a `limit` can be passed in, limiting the
/// parsing to only being done `limit` times.
///
/// The specified closure is invoked with each string that
/// is found, and the number of strings found is returned.
pub unsafe fn from_c_multistring<F>(buf: *const libc::c_char,
                                    limit: Option<usize>,
                                    mut f: F) -> usize
    where F: FnMut(&[u8])
{
    let mut curr_ptr = buf;
    let mut ctr = 0us;
    let (limited_count, limit) = match limit {
        Some(limit) => (true, limit),
        None => (false, 0)
    };
    while (!limited_count || ctr < limit) && *curr_ptr != 0 {
        let len = libc::strlen(curr_ptr) as usize;
        f(slice::from_raw_buf(&(curr_ptr as *const u8), len));
        curr_ptr = curr_ptr.offset(len as isize + 1);
        ctr += 1;
    }
    return ctr;
}

#[cfg(test)]
mod testutil {
    use super::CStrArg;
    use std::iter::range;

    #[inline]
    pub fn check_c_str(c_str: &CStrArg, expected: &[u8]) {
        let buf = c_str.as_ptr();
        let len = expected.len();
        for i in range(0, len) {
            let byte = unsafe { *buf.offset(i as isize) as u8 };
            assert_eq!(byte, expected[i]);
        }
        let term = unsafe { *buf.offset(len as isize) as u8 };
        assert_eq!(term, 0);
    }
}

#[cfg(test)]
mod tests {
    use std::iter::Iterator;
    use std::ptr;
    use libc;
    use super::testutil::check_c_str;

    use super::{CString, CStrArg, IntoCStr, CChars, LibcDtor};
    use super::from_c_multistring;

    fn bytes_dup(s: &[u8]) -> CString<LibcDtor> {
        let len = s.len();
        unsafe {
            let dup = libc::malloc(len as libc::size_t) as *mut u8;
            ptr::copy_nonoverlapping_memory(dup, s.as_ptr(), len);
            *dup.offset(len as isize) = 0;
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

        assert!(invalid.into_c_str().is_err());
    }

    #[test]
    fn test_bytes_into_c_str() {
        test_into_c_str(vec!(b"", b"hello", b"foo\xFF", b"Mary had a little lamb"),
                        &[b"", b"hello", b"foo\xFF", b"Mary had a little lamb"],
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
        let bytes = unsafe { super::parse_as_bytes(c_str.ptr, &c_str) };
        assert_eq!(bytes, b"hello");
        let c_str = str_dup("");
        let bytes = unsafe { super::parse_as_bytes(c_str.ptr, &c_str) };
        assert_eq!(bytes, b"");
        let c_str = bytes_dup(b"foo\xFF");
        let bytes = unsafe { super::parse_as_bytes(c_str.ptr, &c_str) };
        assert_eq!(bytes, b"foo\xFF");
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
    #[should_fail]
    fn test_parse_null_as_bytes_fail() {
        unsafe {
            let p: *const libc::c_char = ptr::null();
            let _ = super::parse_as_bytes(p, &p);
        };
    }

    #[test]
    #[should_fail]
    fn test_str_constructor_fail() {
        let _c_str: CString<LibcDtor> = unsafe {
            CString::from_raw_buf(ptr::null())
        };
    }

    #[test]
    #[should_fail]
    fn test_c_str_arg_from_static_bytes_fail() {
        let _c_str = CStrArg::from_static_bytes(b"no nul\xFF");
    }

    #[test]
    #[should_fail]
    fn test_chars_constructor_fail() {
        let p: *const libc::c_char = ptr::null();
        let _chars = unsafe { CChars::from_raw_ptr(p, &p) };
    }
}

#[cfg(test)]
mod bench {
    use test::Bencher;
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
