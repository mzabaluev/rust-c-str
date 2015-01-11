# C string helpers for Rust

This library resulted from improving the functionality for working
with null-terminated strings that was formerly provided by Rust module
`std::c_str`. Earlier revisions of this work were submitted as an
[RFC](https://github.com/rust-lang/rfcs/pull/435) for inclusion in the Rust
distribution, but a more conservative redesign has been selected instead.

Nonetheless, this crate provides memory management helpers for
foreign-allocated null-terminated strings, as well as performance-minded
conversion methods for producing null-terminated strings out of built-in Rust
strings and related data types. If your code involves a lot of passing string
data between C-style APIs and Rust, you may want to give this library a try.
