struct T(i32);

fn scopes() {
    let mut x = T(4);
    // PCS {x = pack(x.0)}
    {
        x.0 = 3;
        // PCS {} {x.0}
    }
    // PCS {x.0}
    println!("{}", x.0);

    {
        let y = &mut x;
        // PCS s1:{y-w->s0::x} s0:{}
        y.0 = 4;
        // PCS s1:{(y-w->s0::x).0} s0:{} (unpack)
    }
    // PCS s0:{x} (unpack)

    // println!("{}", y.0); Error
}
