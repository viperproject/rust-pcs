struct A;
struct B {
    a1: A,
    a2: A,
}
struct C {
    b: B,
}
struct D {
    c: C,
}

fn consume_call() {
    let a1 = A;
    let a2 = A;
    let b = B { a1, a2 };
    let c = C { b };
    let d = D { c };

    consume(d.c.b.a1); // drop sub-field

    let x = d.c.b.a2; // still accessible
}

fn consume(a: A) {}
