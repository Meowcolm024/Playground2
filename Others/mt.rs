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