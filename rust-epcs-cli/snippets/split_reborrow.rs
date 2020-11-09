struct TreeNode<'a> {
    val: u8,
    left: Option<&'a TreeNode<'a>>,
    right: Option<&'a TreeNode<'a>>,
}

fn split_reborrow() {
    let mut l = TreeNode {
        val: 3,
        left: None,
        right: None,
    };
    let mut n = TreeNode {
        val: 2,
        left: Some(&l),
        right: Some(&l),
    };
    let mut r = TreeNode {
        val: 2,
        left: Some(&n),
        right: Some(&l),
    };

    let mut y = &r;
    // {y, r} with (y->r)
    let z: &Option<&TreeNode> = &y.left;
    // {y.right, y.left, z, r} with (y->r, z->y.left)
    y = &l;
    // {y, z, r} with (@1->r, z->@1.left, y->l)
}
