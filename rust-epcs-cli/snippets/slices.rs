fn slices() {
    let mut a = [0, 1, 2];
    let b = &mut a[..1];
    // a[2] = 3;
    b[0] = 4;
}
