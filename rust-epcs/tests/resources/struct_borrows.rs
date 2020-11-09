struct T<'a> {
    left: &'a i32,
    right: &'a i32,
}

fn struct_borrows() {
    let x = 10;
    let y = 20;
    let a = T{
        left: &x,
        right: &y,
    };

    drop(a);
}