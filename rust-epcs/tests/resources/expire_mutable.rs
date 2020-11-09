struct T {
    inner: i32,
}

fn expire_mutable() {
    let mut x = T{
        inner: 10,
    };

    let y = &mut x.inner;
    let z = &x;
}