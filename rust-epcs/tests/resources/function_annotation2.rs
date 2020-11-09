fn harness() {
    let x = 11;

    let y = choose(&x);
}

fn choose<'a>(left: &u32) -> &u32 {
    left
}
