#[link(name = ":libCpp.a")]
extern "C" {
    // fn fibonacci(n: i32) -> i32;
    fn hello(n: i32);
}

// attempt failed to link with haskell

fn main() {
    unsafe {
        hello(5);
        // println!("fib 10 from Haskell: {}", fibonacci(10));
    }
}