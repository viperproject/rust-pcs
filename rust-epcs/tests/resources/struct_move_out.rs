struct U(i32);
struct T {
    left: U,
    right: U,
}

fn struct_move_out() {
    let mut x = T {
        left: U(1),
        right: U(2),
    };

    let y = &mut x.left;
}