use histutils::{HistoryFile, ShellFormat, parse_entries, write_entries};
use std::env;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::process;

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

    if paths.is_empty() {
        paths.push("-".to_string());
    }

    let history_files: Vec<HistoryFile<Box<dyn BufRead>>> = paths
        .into_iter()
        .map(|p| -> io::Result<HistoryFile<Box<dyn BufRead>>> {
            if p == "-" {
                Ok(HistoryFile {
                    reader: Box::new(BufReader::new(io::stdin())),
                    path: None,
                })
            } else {
                let f = File::open(&p)?;
                Ok(HistoryFile {
                    reader: Box::new(BufReader::new(f)),
                    path: Some(std::path::PathBuf::from(p)),
                })
            }
        })
        .collect::<io::Result<Vec<_>>>()?;

    let history = parse_entries(history_files)?;

    if count {
        println!("{}", history.entries.len());
    } else {
        let detected_format = history.primary_format();
        format = format.or(detected_format);
        if format.is_none() {
            eprintln!("could not detect history format; please specify --format");
            process::exit(1);
        }

        let mut stdout = io::stdout();
        write_entries(&mut stdout, history.entries, format.unwrap())?;
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
