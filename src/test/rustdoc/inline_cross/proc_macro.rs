// aux-build:proc_macro.rs
// build-aux-docs

extern crate some_macros;

// @has proc_macro/index.html
// @has - '//a/@href' 'macro.some_proc_macro.html'
// @has - '//a/@href' 'attr.some_proc_attr.html'
// @has - '//a/@href' 'derive.SomeDerive.html'
// @has proc_macro/macro.some_proc_macro.html
// @has proc_macro/attr.some_proc_attr.html
// @has proc_macro/derive.SomeDerive.html
pub use some_macros::{some_proc_macro, some_proc_attr, SomeDerive};
