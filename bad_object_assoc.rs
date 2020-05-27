use std::fmt;

struct Bar;

trait Foo {
    type Assoc: 'static + fmt::Display;
}

fn foo<T: Foo+?Sized>(t: T::Assoc) -> Box<fmt::Display+'static> {
    Box::new(t)
}

fn wat() -> Box<fmt::Display+'static> {
    let x = Bar;
    foo::<Foo<Assoc=Bar>>(x)
}

fn main() {
    println!("{}", wat());
}
