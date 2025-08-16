use histutils::{ShellFormat, parse_format};
use std::env;
use std::fs::File;
use std::io;
use std::process;

fn main() -> io::Result<()> {
    let mut args = env::args().skip(1);
    let mut format = ShellFormat::ZshExtended;
    let mut paths: Vec<String> = Vec::new();

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                println!("usage: histutils [--format FORMAT] [--version] [FILE...]");
                return Ok(());
            }
            "--version" | "-V" => {
                println!("{}", env!("CARGO_PKG_VERSION"));
                return Ok(());
            }
            "--format" => {
                if let Some(fmt) = args.next() {
                    format = if let Some(f) = parse_format(&fmt) {
                        f
                    } else {
                        eprintln!("unknown format: {fmt}");
                        process::exit(1);
                    };
                } else {
                    eprintln!("--format requires a value");
                    process::exit(1);
                }
            }
            _ if arg.starts_with("--format=") => {
                let fmt = &arg["--format=".len()..];
                format = if let Some(f) = parse_format(fmt) {
                    f
                } else {
                    eprintln!("unknown format: {fmt}");
                    process::exit(1);
                };
            }
            _ => {
                paths.push(arg);
            }
        }
    }

    let entries = if paths.is_empty() {
        histutils::parse_readers([(io::stdin(), "-")])?
    } else {
        let mut readers = Vec::new();
        for p in &paths {
            let f = File::open(p)?;
            readers.push((f, p.clone()));
        }
        histutils::parse_readers(readers)?
    };

    let mut stdout = io::stdout();
    histutils::write_entries(&mut stdout, entries, format)?;

    Ok(())
}
