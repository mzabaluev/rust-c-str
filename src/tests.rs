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

use std::iter::{Iterator, range};
use std::ptr;
use libc;

use super::{CStr, CStrBuf, OwnedCString};
use super::{libc_free, parse_c_multistring};

pub fn check_c_str(c_str: &CStr, expected: &[u8]) {
    let buf = c_str.as_ptr();
    let len = expected.len();
    for i in range(0, len) {
        let byte = unsafe { *buf.offset(i as isize) as u8 };
        assert_eq!(byte, expected[i]);
    }
    let term = unsafe { *buf.offset(len as isize) as u8 };
    assert_eq!(term, 0);
}

unsafe fn bytes_dup_raw(s: &[u8]) -> *const libc::c_char {
    let len = s.len();
    let dup = libc::malloc((len + 1) as libc::size_t) as *mut u8;
    ptr::copy_nonoverlapping_memory(dup, s.as_ptr(), len);
    *dup.offset(len as isize) = 0;
    dup as *const libc::c_char
}

fn bytes_dup(s: &[u8]) -> OwnedCString {
    unsafe {
        OwnedCString::new(bytes_dup_raw(s), libc_free)
    }
}

fn str_dup(s: &str) -> OwnedCString {
    bytes_dup(s.as_bytes())
}

#[test]
fn test_str_multistring_parsing() {
    unsafe {
        let input = b"zero\0one\0\0";
        let ptr = input.as_ptr();
        let expected = ["zero", "one"];
        let mut it = expected.iter();
        let result = parse_c_multistring(ptr as *const libc::c_char, None,
            |cbytes| {
                assert_eq!(cbytes, it.next().unwrap().as_bytes());
            });
        assert_eq!(result, 2);
        assert!(it.next().is_none());
    }
}

#[test]
fn test_c_str_macro() {
    let c_str = c_str!("hello");
    check_c_str(c_str, b"hello");
}

#[test]
fn test_string_deref() {
    let c_str = str_dup("hello");
    check_c_str(&*c_str, b"hello");
}

#[test]
fn test_string_as_ptr() {
    let c_str = str_dup("hello");
    let len = unsafe { libc::strlen(c_str.as_ptr()) };
    assert_eq!(len, 5);
}

#[test]
fn test_iterator() {
    let c_string = str_dup("");
    let mut iter = c_string.iter();
    assert_eq!(iter.next(), None);

    let c_string = str_dup("hello");
    let mut iter = c_string.iter();
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
fn test_parse_as_utf8() {
    let c_str = str_dup("hello");
    let res = unsafe { super::parse_as_utf8(c_str.ptr, &c_str) };
    assert_eq!(res, Ok("hello"));
    let c_str = str_dup("");
    let res = unsafe { super::parse_as_utf8(c_str.ptr, &c_str) };
    assert_eq!(res, Ok(""));
    let c_str = bytes_dup(b"foo\xFF");
    let res = unsafe { super::parse_as_utf8(c_str.ptr, &c_str) };
    assert!(res.is_err());
}

#[test]
fn test_c_str_buf_from_bytes() {
    let c_str = CStrBuf::from_bytes(b"").unwrap();
    check_c_str(&*c_str, b"");

    let c_str = CStrBuf::from_bytes(b"foo\xFF").unwrap();
    check_c_str(&*c_str, b"foo\xFF");

    // Owned variant
    let c_str = CStrBuf::from_bytes(b"Mary had a little \xD0\x0D, Little \xD0\x0D").unwrap();
    check_c_str(&*c_str, b"Mary had a little \xD0\x0D, Little \xD0\x0D");

    let res = CStrBuf::from_bytes(b"got\0nul");
    let err = res.err().unwrap();
    assert_eq!(err.position, 3);
}

#[test]
fn test_c_str_buf_from_str() {
    let c_str = CStrBuf::from_str("").unwrap();
    check_c_str(&*c_str, b"");

    let c_str = CStrBuf::from_str("hello").unwrap();
    check_c_str(&*c_str, b"hello");

    // Owned variant
    let c_str = CStrBuf::from_str("Mary had a little lamb, Little lamb").unwrap();
    check_c_str(&*c_str, b"Mary had a little lamb, Little lamb");

    let res = CStrBuf::from_str("got\0nul");
    let err = res.err().unwrap();
    assert_eq!(err.position, 3);
}

#[test]
fn test_c_str_buf_from_vec() {
    let c_str = CStrBuf::from_vec(b"".to_vec()).unwrap();
    check_c_str(&*c_str, b"");

    let c_str = CStrBuf::from_vec(b"hello".to_vec()).unwrap();
    check_c_str(&*c_str, b"hello");

    // Owned variant
    let c_str = CStrBuf::from_vec(b"Mary had a little lamb, Little lamb".to_vec()).unwrap();
    check_c_str(&*c_str, b"Mary had a little lamb, Little lamb");

    let res = CStrBuf::from_vec(b"got\0nul".to_vec());
    let err = res.err().unwrap();
    assert_eq!(err.nul_error().position, 3);
    let vec = err.into_bytes();
    assert_eq!(vec.as_slice(), b"got\0nul");
}

#[test]
fn test_c_str_buf_into_vec() {
    let c_str = CStrBuf::from_str("").unwrap();
    let vec = c_str.into_vec();
    assert_eq!(vec.as_slice(), b"");
    let c_str = CStrBuf::from_str("hello").unwrap();
    let vec = c_str.into_vec();
    assert_eq!(vec.as_slice(), b"hello");
    let c_str = CStrBuf::from_bytes(b"foo\xFF").unwrap();
    let vec = c_str.into_vec();
    assert_eq!(vec.as_slice(), b"foo\xFF");

    // Owned variant
    let c_str = CStrBuf::from_str("Mary had a little lamb, Little lamb").unwrap();
    let vec = c_str.into_vec();
    assert_eq!(vec.as_slice(), b"Mary had a little lamb, Little lamb");
    let c_str = CStrBuf::from_bytes(b"Mary had a little \xD0\x0D, Little \xD0\x0D").unwrap();
    let vec = c_str.into_vec();
    assert_eq!(vec.as_slice(), b"Mary had a little \xD0\x0D, Little \xD0\x0D");
}

#[test]
fn test_c_str_is_empty() {
    let c_str = CStrBuf::from_str("").unwrap();
    assert!(c_str.is_empty());
}

#[test]
fn test_c_string_parse_as_bytes() {
    let c_str = str_dup("hello");
    assert_eq!(c_str.parse_as_bytes(), b"hello");
    let c_str = str_dup("");
    assert_eq!(c_str.parse_as_bytes(), b"");
    let c_str = bytes_dup(b"foo\xFF");
    assert_eq!(c_str.parse_as_bytes(), b"foo\xFF");
}

#[test]
fn test_c_string_parse_as_utf8() {
    let c_str = str_dup("hello");
    assert_eq!(c_str.parse_as_utf8(), Ok("hello"));
    let c_str = str_dup("");
    assert_eq!(c_str.parse_as_utf8(), Ok(""));
    let c_str = bytes_dup(b"foo\xFF");
    assert!(c_str.parse_as_utf8().is_err());
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
fn test_parse_null_as_utf8_fail() {
    unsafe {
        let p: *const libc::c_char = ptr::null();
        let _ = super::parse_as_utf8(p, &p);
    };
}

#[test]
#[should_fail]
fn test_c_string_new_fail() {
    let _c_str: OwnedCString = unsafe {
        OwnedCString::new(ptr::null(), libc_free)
    };
}

#[test]
#[should_fail]
fn test_from_static_bytes_fail() {
    let _c_str = super::from_static_bytes(b"no nul");
}

#[test]
#[should_fail]
fn test_from_static_str_fail() {
    let _c_str = super::from_static_str("no nul");
}

#[test]
#[should_fail]
fn test_from_raw_ptr_fail() {
    let p: *const libc::c_char = ptr::null();
    let _c_str = unsafe { super::from_raw_ptr(p, &p) };
}

// Do you love me, Travis?
