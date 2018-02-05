// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(nll)]

struct Foo;

impl Foo {

    fn weird_method(&mut self) {
        let mut var = self;

        loop {
            var = match Some(&mut *var) {
                Some(v) => v,
                None => var
            };

            var = var;
            var = var;
            var = var;
        }
    }

}

fn main() {}
