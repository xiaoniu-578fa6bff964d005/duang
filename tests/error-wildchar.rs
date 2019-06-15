use duang::duang;

duang!(
pub fn foo((_a,_):(i32,i32)) {}
);

fn main() {
  foo!((1,2));
}
