// this test check the error message when parameters are not all Captured.
use duang::duang;

struct Unit();

impl Unit {
  duang!(
  pub fn foo<T>(&self, a: T,b: f64 = 13.0, c: T = a*a) -> (T,f64,T)
  where
    T: std::ops::Mul<T, Output = T>,
    T: std::fmt::Display,
    T: Copy,
  {
    (a,b,c)
  }
  );
}

fn main() {
}
