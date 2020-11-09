struct T {
    inner: U,
}

struct U {
    inner: V,
}

struct V {
    inner: i32,
}

fn test() {
    let mut x = T {
        inner: U {
            inner: V {
                inner: 10,
            },
        },
    };

    let a = &x.inner;
    let b = &x.inner.inner;
    let c = &mut x.inner.inner.inner;
}