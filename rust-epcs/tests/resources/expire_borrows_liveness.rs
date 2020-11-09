struct T(u32);

fn expire_borrows_liveness() {
    let mut a = T(1);
    let mut b = T(2);

    let x = &mut a;
    let y = &b;

    a = T(3);
    // Expire x
    b = T(4);
    // Expire y

}