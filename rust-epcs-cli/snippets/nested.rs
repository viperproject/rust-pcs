fn nested(depth: u8) {
    let mut i = 0;
    while i < depth / 2 {
        while i < depth - 2 {
            i = i + 1;
        }
    }
    println!("{}", i)
}
