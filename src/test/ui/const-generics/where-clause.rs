// Tests that 'where' clauses can only contain either plain
// const parameters, or const expressions not involving any parameters
#![feature(const_generics)]

struct OtherStruct<const P: usize> {}
struct SecondStruct<const P: usize, const V: usize, const U: usize> {}

struct One;
struct Two;
struct Three;

trait ParamTrait<const P: bool> {}
trait MyTrait {}
trait ThirdTrait {}

impl<const P: usize> MyTrait for SecondStruct<{
    // Please don't ever actually do this
    let b: OtherStruct<{P}>;
    42
}, {P}, {P + 1}> {}

impl<const P: usize> MyTrait for OtherStruct<{P}> where One: ParamTrait<{P + 1}> {}
impl<const P: usize> ThirdTrait for OtherStruct<{P + 1}> {}


impl<const P: bool> ParamTrait<{P | true}> for One {}
// ~^ ERROR 
impl<const P: bool> ParamTrait<{P}> for Two {}
impl ParamTrait<{true & false}> for Three {}

fn main() {}
