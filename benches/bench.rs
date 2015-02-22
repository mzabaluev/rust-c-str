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

#![feature(test)]

extern crate c_string;

extern crate test;

use test::Bencher;

use c_string::CStrBuf;

static S_SHORT: &'static str = "Mary";
static S_MEDIUM: &'static str = "Mary had a little lamb, Little lamb";
static S_LONG: &'static str = "\
    Mary had a little lamb, Little lamb
    Mary had a little lamb, Little lamb
    Mary had a little lamb, Little lamb
    Mary had a little lamb, Little lamb
    Mary had a little lamb, Little lamb
    Mary had a little lamb, Little lamb";

fn bench_c_str_buf_from_str(b: &mut Bencher, s: &str) {
    b.iter(|| {
        CStrBuf::from_str(s)
    });
}

#[bench]
fn bench_c_str_buf_from_str_short(b: &mut Bencher) {
    bench_c_str_buf_from_str(b, S_SHORT);
}

#[bench]
fn bench_c_str_buf_from_str_medium(b: &mut Bencher) {
    bench_c_str_buf_from_str(b, S_MEDIUM);
}

#[bench]
fn bench_c_str_buf_from_str_long(b: &mut Bencher) {
    bench_c_str_buf_from_str(b, S_LONG);
}

fn bench_c_str_buf_from_vec_and_back(b: &mut Bencher, s: &str) {
    let mut shelf: Option<Vec<u8>> = Some(s.as_bytes().to_vec());
    b.iter(move || {
        let vec = shelf.take().unwrap();
        let c_str = CStrBuf::from_vec(vec).unwrap();
        shelf = Some(c_str.into_vec());
    });
}

#[bench]
fn bench_c_str_buf_from_vec_and_back_short(b: &mut Bencher) {
    bench_c_str_buf_from_vec_and_back(b, S_SHORT);
}

#[bench]
fn bench_c_str_buf_from_vec_and_back_medium(b: &mut Bencher) {
    bench_c_str_buf_from_vec_and_back(b, S_MEDIUM);
}

#[bench]
fn bench_c_str_buf_from_vec_and_back_long(b: &mut Bencher) {
    bench_c_str_buf_from_vec_and_back(b, S_LONG);
}

fn bench_c_str_buf_from_vec_unchecked_and_back(b: &mut Bencher, s: &str) {
    let mut shelf: Option<Vec<u8>> = Some(s.as_bytes().to_vec());
    b.iter(move || {
        let vec = shelf.take().unwrap();
        let c_str = unsafe { CStrBuf::from_vec_unchecked(vec) };
        shelf = Some(c_str.into_vec());
    });
}

#[bench]
fn bench_c_str_buf_from_vec_unchecked_and_back_short(b: &mut Bencher) {
    bench_c_str_buf_from_vec_unchecked_and_back(b, S_SHORT);
}

#[bench]
fn bench_c_str_buf_from_vec_unchecked_and_back_medium(b: &mut Bencher) {
    bench_c_str_buf_from_vec_unchecked_and_back(b, S_MEDIUM);
}

#[bench]
fn bench_c_str_buf_from_vec_unchecked_and_back_long(b: &mut Bencher) {
    bench_c_str_buf_from_vec_unchecked_and_back(b, S_LONG);
}
