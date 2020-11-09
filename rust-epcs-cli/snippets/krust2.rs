fn krust2() {
    let mut x;
    {
        let y = 1;
        x = &y; //Error!
        println!("{}", y);
        println!("{}", x);
    }
    // let new = x; // New line to get the error alluded to in the paper, otherwise x is not used out of y's scope
    let z = 1;
    let p = &z; //OK!
}
