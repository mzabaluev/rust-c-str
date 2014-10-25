// Copyright 2014 Mikhail Zabaluev <mikhail.zabaluev@gmail.com>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![crate_name = "c_compat"]
#![crate_type = "lib"]

#![feature(default_type_params)]

extern crate alloc;
extern crate libc;

#[cfg(test)]
extern crate test;

pub mod c_str;