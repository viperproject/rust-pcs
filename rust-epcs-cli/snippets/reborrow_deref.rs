struct T(i32);

struct Simple {
    a: T,
    b: u8,
}

fn reborrow_deref() {
    let mut t = Simple { a: T(2), b: 0 };
    let mut w = Simple { a: T(3), b: 1 };
    let mut x = Simple { a: T(4), b: 2 };
    // {x}
    let mut y = &mut x;
    // {y} with (y->x)
    let z: &mut &mut Simple = &mut y;
    // {y, z} with (y->x, z->y)
    // y = &mut w; // can't change y because borrowed by z
    *z = &mut w;
    // {z} with (y->w, z->y)

    println!("{}", z.a.0);
    println!("{}", y.a.0);
    println!("{}", x.a.0);
}
