struct T(i32);
struct Simple {
    a: T,
    b: u8,
}

fn prefix() {
    let mut x = Simple { a: T(1), b: 2 };
    let y = x.a;
    x.a = T(3);
    let mut x2 = x;
    x2.a = T(4);
    println!("{}", y.0);
}
