use std::io;

fn main() {
    let mut buffer = String::new();
    io::stdin().read_line(&mut buffer).expect("input error!");
    let x = buffer.trim().parse::<i32>().unwrap_or_else(|_| 0);
    println!("{}", x);
}