struct T<'a> {
    inner: &'a u32,
    outer: &'a u32,
}
fn harness() {
    let mut x = T{ inner: &11, outer: &12 };
    let mut y = T{ inner: &30, outer: &31 };

    swap(&mut x, &mut y);
}

fn swap<'a> (one: &mut T<'a>, two: &mut T<'a>) {
    one.inner = two.inner
}