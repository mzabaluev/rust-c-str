# c_str! macro for Rust

This macro-only crate provides the `c_str!` macro to facilitate creation
of C-compatible string values from Rust string literals.

## Legacy code

This repository also contains source code for crate `c_string`,
which is no longer maintained. It provided some utility types to
facilitate working with C-compatible strings in Rust, but most of
them were poorly designed or do not fit well with the evolution
of the language. The topmost commit for that crate is available
under branch `c-string`.
