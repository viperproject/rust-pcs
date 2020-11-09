//#[derive(Debug)]
struct LinkedListNode {
    next: Option<Box<LinkedListNode>>,
    value: i32,
}

fn append(root: &mut Option<Box<LinkedListNode>>, new: i32) -> &mut Option<Box<LinkedListNode>> {
    let mut cur = root;

    while let Some(ref mut node) = cur {
        cur = &mut node.next;
        let v = &mut node.value;
    }
    
    *cur = Some(Box::new(LinkedListNode{
        next: None,
        value: new,
    }));
    
    cur
}

/*fn main() {
    let mut x = Some(Box::new(LinkedListNode{
        next: Some(Box::new(LinkedListNode{
            next: Some(Box::new(LinkedListNode{
                next: None,
                value: 3,
            })),
            value: 2,
        })),
        value: 1,
    }));
    
    append(&mut x, 4);
    
    println!("{:?}", x);
}*/