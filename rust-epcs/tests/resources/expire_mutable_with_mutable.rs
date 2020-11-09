struct T(i32);
fn expire_shared_with_mutable() {
    let mut x = T(10);
    let y = &mut x;
    let z = &mut x;
    // Borrow y should have been expired by now
}