pub fn borrow() {
    let mut a = 6;
    let x = &mut a;
    *x = 4;
    assert!(a == 4);
}
