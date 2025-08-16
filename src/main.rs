use histutils::{ShellFormat, detect_format};
use std::env;
use std::fs::File;
use std::io::{self, Read, Seek};
use std::process;

trait ReadSeek: Read + Seek {}
impl<T: Read + Seek> ReadSeek for T {}

fn main() -> io::Result<()> {
    let mut args = env::args().skip(1);
    let mut format: Option<ShellFormat> = None;
    let mut paths: Vec<String> = Vec::new();
    let mut count = false;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                println!("usage: histutils [--format FORMAT] [--count] [--version] [FILE...]");
                return Ok(());
            }
            "--version" | "-V" => {
                println!("{}", env!("CARGO_PKG_VERSION"));
                return Ok(());
            }
            "--count" | "-c" => {
                count = true;
            }
            "--format" => {
                if let Some(fmt) = args.next() {
                    format = if let Some(f) = parse_format_opt(&fmt) {
                        Some(f)
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
                format = if let Some(f) = parse_format_opt(fmt) {
                    Some(f)
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

    let mut inputs: Vec<(Box<dyn ReadSeek>, String)> = Vec::new();
    if paths.is_empty() {
        let mut buf = Vec::new();
        io::stdin().read_to_end(&mut buf)?;
        inputs.push((Box::new(io::Cursor::new(buf)), "-".to_string()));
    } else {
        for p in paths {
            let f = File::open(&p)?;
            inputs.push((Box::new(f), p));
        }
    }

    if format.is_none() {
        let detected = detect_format(inputs.iter_mut().map(|(r, _)| r.as_mut()))?;
        format = detected;
        if format.is_none() {
            eprintln!("could not detect history format; please specify --format");
            process::exit(1);
        }
    }

    let entries = histutils::parse_readers(inputs.into_iter())?;

    if count {
        println!("{}", entries.len());
    } else {
        let mut stdout = io::stdout();
        histutils::write_entries(&mut stdout, entries, format.unwrap())?;
    }

    Ok(())
}

fn parse_format_opt(s: &str) -> Option<ShellFormat> {
    match s {
        "sh" | "bash" => Some(ShellFormat::Sh),
        "zsh" | "zsh-extended" | "zsh_extended" => Some(ShellFormat::ZshExtended),
        "fish" => Some(ShellFormat::Fish),
        _ => None,
    }
}
