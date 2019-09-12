extern crate pdx_txt;

use std::{env, fs::File, io::Read, process::exit};

pub fn usage(arg0: &str) {
    println!("USAGE: {} <file>", arg0);
}

pub fn main() -> std::io::Result<()> {
    let args: Vec<_> = env::args().collect();

    if args.len() != 2 {
        usage(&args[0]);
        exit(1);
    }

    let mut file = File::open(&args[1])?;
    let mut data = String::new();
    file.read_to_string(&mut data)?;

    let x = pdx_txt::parse(&data).unwrap();
    println!("{:?}", x);

    Ok(())
}
