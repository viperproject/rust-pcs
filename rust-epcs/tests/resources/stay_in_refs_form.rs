struct T<'a>(&'a U);
struct U(i32);

fn testr<'a>(a: &mut T<'a>, b: &mut T<'a>) {}

fn test() {
    let x = U(10);
    let y = U(20);
    let z = U(30);
    
    let mut a = T(&x);
    let mut b = T(&y);
    
    testr(&mut a, &mut b);
    
    a.0 = &z;
    // refs(a, 'a) -> x, a.0 -> z
}