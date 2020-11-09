struct T(u32);

fn simple_if(x: u32) {
    let a = T(10);
    let b = T(7);

    let r = if x > 11 {
        &a
    } else {
        &b
    };
}