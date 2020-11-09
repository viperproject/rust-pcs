fn lt_user<'a>(x: &'a mut u8, y: &'a u8) -> &'a mut u8 {
    return x;
}

fn shared_lifetime() {
    let mut pp = 7;
    let mut rr = 8;
    let mut ss = 9;
    let mut p = &mut pp;
    let mut s = &mut ss;
    // PCS {s, p, rr} (s->ss, p->pp)
    let q = lt_user(s, p);
    // PCS {q, p} (q->[lifetime(p) == lifetime(s)], p->pp, s->ss)
    // pp = rr; // ERROR because pp isn't in the PCS
    print!("{}", q);
    // q released here, as are p and s -- we should get this from the borrow checker
    // {pp rr ss}
}
