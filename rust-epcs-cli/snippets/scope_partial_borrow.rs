struct T(i32);
struct A;
struct B {
    a1: A,
    a2: A,
}

fn scope_partial_borrow() {
    let x: u8 = 3; // let
    let y = x; // Copy

    let z = T(4);
    let a = z; // Move

    let a1 = A;
    // Scope
    {
        let a2 = A;
        let mut b = B { a1, a2 };
        consume(b.a1); // Partial Move
        let c = &mut b.a2; // Mutable Borrow
        *c = A;
        let d = &c; // Immutable reborrow
        d; // Borrow Expiry
        b.a2 = A;
    }
}

fn consume(a: A) {}
