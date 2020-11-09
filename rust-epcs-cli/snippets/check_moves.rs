struct T(i32);
fn check_moves() {
    let mut x = T(5);
    let y = x;
    x = T(6);
    assert!(y.0 == 5);
}
