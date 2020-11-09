fn nested_cond(depth: u8) {
    let mut i = 0;
    while i < {
        while i < depth - 2 {
            i = i + 1;
        }
        depth - i
    } {
        i = i + 2
    }
    println!("{}", i)
}
