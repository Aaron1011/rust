use std::fmt;

trait Foo {
    type Assoc: 'static;
}

fn foo<T: Foo+?Sized>(t: T::Assoc) -> Box<fmt::Display+'static>
        where T::Assoc: fmt::Display {
    Box::new(t)
}

fn wat() -> Box<fmt::Display+'static> {
    let x = 42;
    foo::<Foo<Assoc=&u32>>(&x)
}

fn main() {
    println!("{}", wat());
}
