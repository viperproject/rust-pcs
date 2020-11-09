struct Node<'a> {
    val: u8,
    next: &'a Node<'a>,
}

fn simplest_loop(m: &mut Node) -> u8 {
    let mut n = &*m;
    let mut v = &m.val;
    while (n.val > 0) {
        n = n.next;
        v = &n.val;
    }
    return *v;
}