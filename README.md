# C string helpers for Rust

This library implements improvements over Rust's FFI facilities for
null-terminated strings, as proposed in these RFCs:

* https://github.com/rust-lang/rfcs/pull/592
* https://github.com/rust-lang/rfcs/pull/840

On top of that, this crate provides RAII memory management helpers for
foreign-allocated C-style strings, as well as more convenient transformation
functions and macros that did not pass the rigors of the RFC process for
inclusion in the Rust standard library.
