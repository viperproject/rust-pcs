fn harness() {
    let x = 11;
    let y = 30;

    let z = choose(&x, &y);
}

fn choose<'a>(left: &'a u32, right: &'a u32) -> &'a u32 {
    left
}
