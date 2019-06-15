# duang

Rust doesn't support either default function arguments or named function arguments.

This crate generates a macro interface for a given function that can be invoked with named arguments and fills default argument values, while keeping the original function intact.

## Generating a macro interface

In order to generate a macro for a function, we just need to wrap its definition with `duang!{...}`:

```rust
use duang::duang;

duang!(
pub fn foo<T>(a: T, b: f64 = 13.0, c: T = a * a) -> (T, f64, T)
where
  T: std::ops::Mul<T, Output = T>,
  T: std::fmt::Display,
  T: Copy,
{
  (a, b, c)
}
);
```

## Invocation

The function can then be called through its macro interface, which will handle parameter dispatch and common error detection:

```rust
use demo_duang::foo;
// pass
assert_eq!(foo!(1, c = 30, b = -2.0), (1, -2.0, 30));
// pass
assert_eq!(foo!(a = 10), (10, 13.0, 100));
// fail
// foo!(1,c=30,c=2);
```

The original function can still be called with the usual syntax:
```rust
use demo_duang::foo;
assert_eq!(foo(1, 2.0, 3), (1, 2.0, 3));
```

## Features
- Supports generics and existential types.
- Friendly error messages.

## Common issues
### Use local variable in default value.
In order to use the generated macro in another crate, users should add `$crate` and path of the variable used.
The variable should also be visible (`pub`) to the scope where the macro is invoked.

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
- Doesn't support associated functions.
- The wildcard pattern `_` cannot be used in pattern argument. For example, `fn foo((a, _): (i32, i32))` is illegal.

## TODO
- Generate document for function or macro.
- After "Attributes in formal function parameter position"([#60406](https://github.com/rust-lang/rust/issues/60406)) stabilizes, change function-like macros to attribute-like macros.

License: MIT
