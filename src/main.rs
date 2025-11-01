use std::fs;
use std::env;

fn main() -> std::io::Result<()>{
    let args: Vec<String> = env::args().collect();
    let file_path = &args[1];

    let contents = fs::read_to_string(file_path)
        .expect("Should have been able to read the file");

    println!("{}", contents);
    Ok(())
}
