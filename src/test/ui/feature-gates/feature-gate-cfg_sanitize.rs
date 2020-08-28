#[cfg(not(sanitize = "thread"))]
//~^ `cfg(sanitize)` is experimental
//~| `cfg(sanitize)` is experimental
fn main() {}
