// check-pass
#![warn(macro_trailing_semicolon)]

#[allow(dead_code)]
macro_rules! foo {
    ($val:ident) => {
        true; //~ WARN trailing
              //~| WARN this was previously
              //~| WARN trailing
              //~| WARN this was previously
    }
}

fn main() {
    // This `allow` doesn't work
    #[allow(macro_trailing_semicolon)]
    let _ = {
        foo!(first)
    };

    // This 'allow' doesn't work either
    #[allow(macro_trailing_semicolon)]
    let _ = foo!(second);

    // But this 'allow' does
    #[allow(macro_trailing_semicolon)]
    fn inner() {
        let _ = foo!(third);
    }
}
