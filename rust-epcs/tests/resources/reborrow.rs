struct T(i32);

struct Simple {
    a: T,
    b: u8,
}

fn reborrow() {
    let mut w = Simple { a: T(3), b: 1 };
    let mut x = Simple { a: T(4), b: 2 };
    // {x}
    let mut y = &mut x;
    // let mut y = x; // if we make y not a ref
    // {y} with (y->x)
    let z = &mut y.a;
    // this is tricky because of auto-dereferencing, but it borrows from (*y).a which is actually x.a
    // {y.b, z} with (y->x, z->x.a)
    y = &mut w;
    // y = w; // if we make y not a ref, this line fails because y.a is borrowed from y
    // {y, z} with (y->w, z->x.a)
}
