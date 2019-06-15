// this test check the error message when user repeatedly assign to same parameter.
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

fn main() {
  foo!(1,c=1,c=1);
  foo!(1,c=1,a=1);
}
