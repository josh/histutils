use histutils::ShellFormat;
use std::env;
use std::fs::File;
use std::io;
use std::process;

fn parse_format(s: &str) -> Option<ShellFormat> {
    match s {
        "sh" | "bash" => Some(ShellFormat::Sh),
        "zsh" | "zsh-extended" | "zsh_extended" => Some(ShellFormat::ZshExtended),
        "fish" => Some(ShellFormat::Fish),
        _ => None,
    }
}

fn main() -> io::Result<()> {
    let mut args = env::args().skip(1);
    let mut format = ShellFormat::ZshExtended;
    let mut path: Option<String> = None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                println!("usage: histutils [--format FORMAT] [--version] [FILE]");
                return Ok(());
            }
            "--version" | "-V" => {
                println!("{}", env!("CARGO_PKG_VERSION"));
                return Ok(());
            }
            "--format" => {
                if let Some(fmt) = args.next() {
                    format = match parse_format(&fmt) {
                        Some(f) => f,
                        None => {
                            eprintln!("unknown format: {fmt}");
                            process::exit(1);
                        }
                    };
                } else {
                    eprintln!("--format requires a value");
                    process::exit(1);
                }
            }
            _ if arg.starts_with("--format=") => {
                let fmt = &arg["--format=".len()..];
                format = match parse_format(fmt) {
                    Some(f) => f,
                    None => {
                        eprintln!("unknown format: {fmt}");
                        process::exit(1);
                    }
                };
            }
            _ => {
                if path.is_none() {
                    path = Some(arg);
                } else {
                    eprintln!("unexpected argument: {arg}");
                    process::exit(1);
                }
            }
        }
    }

    let entries = if let Some(path) = path {
        let f = File::open(&path)?;
        histutils::parse_reader_with_path(f, &path)?
    } else {
        histutils::parse_reader(io::stdin())?
    };

    let mut stdout = io::stdout();
    histutils::write_entries(&mut stdout, entries, format)?;

    Ok(())
}
