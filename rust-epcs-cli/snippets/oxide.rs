fn oxide() {
    // Rust Oxide 4.2 Conditional Control Flow
    let mut m: u32 = 6;
    // PCS { m }
    let mut n: u32 = 5;
    // PCS { m, n }
    let mut x: &u32 = &n;
    // PCS { x->n, m, n }
    if false {
        x = &m;
        // PCS [{ }] { x->m, m, n }
    }
    // &mut m; Error
    println!("{}", x);
}
