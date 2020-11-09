struct T(i32);

struct SimpleR<'a> {
    a: &'a mut T,
    b: u8,
}

struct Simple {
    a: T,
    b: u8,
}

fn subplaces() {
    let mut a = T(3);
    let b = 4;
    let c = Simple { a, b };

    // println!("{}", c.a.0);
    // println!("{}", a.0); Error, moved!
    // c.a.0 = 3;
    //  c.b = 3;
    let mut a = T(3);
    let b = &a;
    // a.0 = 4; Error, borrowed!

    let mut o = T(3);
    // PCS: {o.0}
    // PCS: {o = pack(o.0)}
    let a = &mut o;
    // PCS {(a->o):w}
    let mut b = 4;
    // PCS {(a->o):w, b}
    let c = SimpleR { a, b };
    // PCS { c.(a->o):w, c.b }
    // PCS { c = pack[(c.a->o):w, c.b] }

    // c.b = 2; Error
    c.a.0 = 3;
    // PCS { c.(a-w->o), c.b } (unpack)
    // PCS { c.(a-w->o).0, c.b:r } (unpack)
    // c.a = &mut T(4); Error!
}
