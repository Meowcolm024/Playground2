fn hello(i: i32) -> i32 {
    match i {
        0 => 1,
        1 => -1,
        n => n*n,
    }
}

fn main() {
    let x = hello(3);
}

enum Tree {
    Leaf(),
    Node(i32 value, Box<Tree> left, Box<Tree> right),
}
