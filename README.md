# duang

Rust doesn't support default function arguments and named function arguments.

This crate generate an macro interface for a given function that can be invoked with named arguments and fill the default argument, meanwhile keep the old function intact.

## Generating macro interface

In order to generate macro for a function, we just need to wrap the definition with `duang!{...}`.

```rust
use duang::duang;

duang!(
pub fn foo<T>(a: T,b: f64 = 13.0, c: T = a*a) -> (T,f64,T)
where
  T: std::ops::Mul<T, Output = T>,
  T: std::fmt::Display,
  T: Copy,
{
  (a,b,c)
}
);
```

## Invoke

```rust
use demo_duang::foo;
// pass
assert_eq!(foo!(1, c = 30, b = -2.0), (1, -2.0, 30));
// pass
assert_eq!(foo!(a = 10), (10, 13.0, 100));
// fail
// foo!(1,c=30,c=2);
```

## Features
- Support generics, existensial type.
- Friendly error message.

## Common issues
### Use local variable in default value.
In order to use the generated macro in other crate, users should add `$crate` and path of the variable used.
Also, the variable should be visible(`pub`) for the scope where the macro is invoked.

```rust
mod bar {
  use duang::duang;
  pub static NUM: i32 = 42;
  duang!(
  pub fn foo(a: i32 = $crate::bar::NUM) -> i32 { a }
  );
}
fn main() {
  use bar::foo;
  assert_eq!(foo!(), 42);
}
```


## Limitations
- Don't support associated function.
- Wildchar can not be used in pattern argument. For example `fn foo((a,_): (i32, i32))` is illegal.

## TODO
- Generate document for function or macro.
- After "Attributes in formal function parameter position"([#60406](https://github.com/rust-lang/rust/issues/60406)) stabilize, change function-like macros to attribute-like macros.

License: MIT
