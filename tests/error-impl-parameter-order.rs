// this test check the error message when mandatory argument come after default ones.
use duang::duang;

duang!(
pub fn foo<T>(a: T,b: f64 = 13.0, c: T) -> (T,f64,T)
where
  T: std::ops::Mul<T, Output = T>,
  T: std::fmt::Display,
  T: Copy,
{
  (a,b,c)
}
);

fn main() {
}
