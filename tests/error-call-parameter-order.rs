// this test check error message when unnamed parameter comes after named ones.
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
  foo!(a=1,0.1);
}
