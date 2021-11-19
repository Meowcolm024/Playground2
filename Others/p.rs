use std::io;

struct Hi;

impl Hello for Hi {
    fn sayHello(&self) {
        println!("hello")
    }
}

trait Hello {
    fn sayHello(&self);

    fn sayMany(&self) {
        for i in 0.. 10 {
            self.sayHello();
        }
    }
}

fn maxxx<'a>(x: &'a i32, y: &'a i32) -> &'a i32 {
    if x > y {
        x
    } else {
        y
    }
}

fn main() {
    let mut buffer = String::new();
    io::stdin().read_line(&mut buffer).expect("input error!");
    let x = buffer.trim().parse::<i32>();
    println!("{}", x.unwrap_or_else(|_| 0));
    let x = Hi;
    x.sayMany();
    let a = 1;
    let b = 2;
    println!("{}", maxxx(&a, &b));
}