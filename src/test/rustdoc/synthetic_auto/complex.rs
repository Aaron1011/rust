mod foo {
    pub trait MyTrait<'a> {
        type MyItem: ?Sized;
    }


    pub struct Inner<'a, Q, R: ?Sized> {
        field: Q,
        field3: &'a u8,
        my_foo: Foo<Q>,
        field2: R,
    }

    pub struct Outer<'a, T, K: ?Sized> {
        my_inner: Inner<'a, T, K>
    }


    pub struct Foo<T> {
        myfield: T
    }
}

// @has complex/struct.NotOuter.html
// @has - '//*[@id="synthetic-implementations-list"]/*[@class="impl"]/*/code' "impl<'a, T, K: ?Sized> Send for NotOuter<'a, T, K> where 'a: 'static, K: for<'b> Fn((&'b bool, &'a u8)) -> &'b i8, <T as MyTrait<'a>>::MyItem: Copy,  T: MyTrait<'a>"

pub use foo::{MyTrait as NotMyTrait, Inner as NotInner, Outer as NotOuter, Foo};

unsafe impl<T> Send for Foo<T> where T: NotMyTrait<'static> {}

unsafe impl<'a, Q, R: ?Sized> Send for NotInner<'a, Q, R> where Q: NotMyTrait<'a>, <Q as NotMyTrait<'a>>::MyItem: Copy, /*for<'b>*/ R: for<'b> Fn((&'b bool, &'a u8)) -> &'b i8, Foo<Q>: Send {}
