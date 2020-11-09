enum T<'a> {
    TwoRefs(&'a U, &'a U)
}

struct U(i32);

fn enum_split_borrows() {
    let a = U(1);
    let b = U(2);

    let x = T::TwoRefs(&a, &b);

    if let T::TwoRefs(left, right) = x {
        drop(a);
        //drop(right);
    }
}