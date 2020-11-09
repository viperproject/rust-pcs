struct NodeM<'a> {
    val: u8,
    next: Option<&'a mut NodeM<'a>>,
}

fn why_old_outer(depth: u8) {
    fn why_old<'a>(mut n: &'a mut NodeM, depth: u8) {
        let mut iterations = 0;
        while iterations < depth {
            if n.next.is_some() {
                n = n.next.as_mut().unwrap();
            }

            iterations = iterations + 1;
        }

        println!("{}", n.val);
    }

    let mut c = NodeM { val: 3, next: None };
    let mut b = NodeM {
        val: 2,
        next: Some(&mut c),
    };

    let mut a = NodeM {
        val: 1,
        next: Some(&mut b),
    };

    why_old(&mut a, depth);
}
