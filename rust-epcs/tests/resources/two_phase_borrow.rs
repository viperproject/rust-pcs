fn two_phase_borrow() {
    let mut v = Vec::new();
    v.push(v.len());
}