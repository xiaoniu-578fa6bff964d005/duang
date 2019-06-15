// this test check the macro exist
use duang::duang;

duang!(
pub fn foo<T>(a: T,b: f64 = 13.0, c: T = a*a)
where
  T: std::ops::Mul<T, Output = T>,
  T: std::fmt::Display,
  T: Copy,
{
  let _result = (a,b,c);
}
);

fn main() {
  foo!(a=10);
}
