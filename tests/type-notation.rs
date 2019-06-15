use duang::duang;

duang!(
pub fn foo(a: impl Default + Clone = Default::default())
{
  let _ = a.clone();
}
);

fn main() {
  foo!(a: i32);
}
