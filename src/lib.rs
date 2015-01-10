// Copyright 2014 Mikhail Zabaluev <mikhail.zabaluev@gmail.com>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! # C compatibility helpers
//!
//! This library provides utilities for working with foreign function
//! interfaces using data layout and allocation conventions of the
//! C language.

#![crate_name = "c_compat"]
#![crate_type = "lib"]

#![allow(unstable)]
#![allow(unstable_features)]

#![feature(unsafe_destructor)]

extern crate libc;

#[cfg(test)]
extern crate test;

pub mod c_str;
