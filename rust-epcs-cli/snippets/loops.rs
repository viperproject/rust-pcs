struct Node<'a> {
    val: u8,
    next: Option<&'a Node<'a>>,
}

fn loops(depth: u8) {
    // PCS: { depth } // omitted from hereon to keep things simple
    let c = Node { val: 3, next: None };
    // PCS: { c = pack(c.val, c.next) }
    let b = Node {
        val: 2,
        // PCS: { b.val }
        next: Some(&c),
        // PCS: { b.val, b.next = pack(b.next.0) } with (b.next.0 -> c)
    };

    // PCS: { b = pack(b.next, b.val), c } with (b.next.0 -> c)
    let a = Node {
        val: 1,
        next: Some(&b),
    };
    // PCS: {a, b, c} with (a.next.0 -> b, b.next.0 -> c)

    let mut iterations = 0;
    // iterations will be omitted for clarity as well

    let mut n = &a;
    // PCS: {n, a, b, c} with (n -> a, a.next.0 -> b, b.next.0 -> c)

    while iterations < depth {
        // Place Invariant: (n->subplaces(a))
        //    It trivially holds on entry
        // PCS {} {n, a, b, c} with () (n->a, a.next.0->b, b.next.0->c))

        n = match n.next {
            // unpacking n, PCS: {} {n.next, n.val, a, b, c} with the same references
            Some(ref_n) => ref_n,
            // unpacking a.next { n.next.0, n.val, a, b, c } with the same references
            None => n,
        };
        // PCS { } {n, a, b, c} with ( n->[old(n) || old(n).next.0] ) (n->a, a.next.0 -> b, b.next.0 -> c))
        iterations = iterations + 1;
        // using the invariant for old(n):
        //     ( n->[subplaces(a) || subplaces(a).next.0], etc. )
        //     ( n->[subplaces(a)], etc. )
        //     Which gives us back the invariant, thus, by induction it's truly an invariant
    }
    // PCS {n, a, b, c} with (n->subplaces(a), a, b, c)

    println!("{}", n.val);
}
