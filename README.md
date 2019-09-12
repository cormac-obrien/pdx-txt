# pdx-txt

A parser for the text format used by Paradox's Clausewitz engine.

# Example usage

```rust
extern crate pdx_txt;

use std::{fs::File, io::Read};

pub fn main() {
    let mut f = File::open("area.txt").expect("Failed to open file");
    let mut data = String::new();
    f.read_to_string(&mut data).expect("Failed to read file");
    let p = pdx_txt::parse(&data).expect("Failed to parse data");
    println!("{:?}", p);
}
```
