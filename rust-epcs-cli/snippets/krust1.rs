fn krust1() {
    let x1 = 1;
    let p1 = &x1; //x1  i s  borrowed  immutably
    let q1 = &x1; //x1  i s  borrowed  immutably
                  // *p1 = 2; //Error !
                  //let y = &mut x1; //Error !
    let mut x2 = 1;
    let p2 = &x2; //x2  i s  borrowed  immutably
    let q2 = &x2; //x2  i s  borrowed  immutably
                  // *p2 = 2; //Error !
    let mut x3 = 1;
    let p3 = &mut x3; //x3  i s  borrowed  mutably
                      // x3 = 2; //Error !
    *p3 = 2; //OK!
    let p4 = &mut x3; //Error in paper, but not anymore b/c of non-lexical lifetimes!
}
