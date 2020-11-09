struct S (i32);

struct T {
    left: S,
    right: S,
}

fn main() {
    let a = T {
        left: S(10),
        right: S(11),
    };

    let b = &a.left;

    drop(a);
}