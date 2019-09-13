use encoding::{
    all::WINDOWS_1252,
    types::{DecoderTrap, Encoding},
};
use pdx_txt;
use std::{
    env,
    fs::File,
    io::{Read, Write},
    process::exit,
};

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
    let mut data = Vec::new();
    file.read_to_end(&mut data)?;

    let input = match WINDOWS_1252.decode(&data, DecoderTrap::Strict) {
        Ok(i) => i,
        Err(msg) => {
            println!("{}", msg);
            exit(1);
        }
    };

    print!("Beginning parse...");
    std::io::stdout().flush().unwrap();
    let _ = match pdx_txt::parse(&input) {
        Ok(x) => x,
        Err(msg) => {
            println!("{}", msg);
            exit(1);
        }
    };
    println!("done.");

    Ok(())
}
