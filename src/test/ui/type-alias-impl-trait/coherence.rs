// aux-build:foreign-crate.rs
// This test ensures that an opaque type cannot be used
// to bypass the normal orphan impl rules.
// Specifically, it should not be possible to implement
// a trait for a local opaque type which resolves to a foreign type.
//
// This should also be prevented by the fact that writing impls for opaque
// types is not allowed at all, but this test makes sure to test
// the orphan rule specifically
#![feature(type_alias_impl_trait)]

extern crate foreign_crate;

trait LocalTrait {}
impl<T> LocalTrait for foreign_crate::ForeignType<T> {}

type AliasOfForeignType<T> = impl LocalTrait;
fn use_alias<T>(val: T) -> AliasOfForeignType<T> {
    foreign_crate::ForeignType(val)
}

impl<T> foreign_crate::ForeignTrait for AliasOfForeignType<T> {}
//~^ ERROR the type parameter `T` is not constrained by the impl trait, self type, or predicates

fn main() {}
