struct T {}
struct S<'a> {f: &'a mut T, g: &'a mut T}
#[allow(unused)]
fn main() {
    let mut y = T {};
    let mut z = T {};
    let mut f = &mut y;
    let mut g = &mut z;
    let r = S { f, g };
}
