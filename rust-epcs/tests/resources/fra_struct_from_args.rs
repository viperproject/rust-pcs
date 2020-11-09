struct U(i32);

struct T<'a> {
    left: &'a U,
    right: &'a U,
}

fn struct_from_args<'a>(left: &'a U, right: &'a U) -> T<'a> {
    T{
        left,
        right,
    }
}

fn main() {
    let x = U(10);
    let y = U(20);

    let z = struct_from_args(&x, &y);
}