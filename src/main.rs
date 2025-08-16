use histutils::{HistoryFile, ShellFormat, detect_format, parse_entries, write_entries};
use std::env;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Read, Seek};
use std::process;

trait ReadSeek: BufRead + Seek {}
impl<T: BufRead + Seek> ReadSeek for T {}

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

    let mut history_files: Vec<HistoryFile<Box<dyn ReadSeek>>> = Vec::new();
    for p in paths {
        if p == "-" {
            let mut buf = Vec::new();
            io::stdin().read_to_end(&mut buf)?;
            history_files.push(HistoryFile {
                reader: Box::new(io::Cursor::new(buf)),
                path: Some(std::path::PathBuf::from("-")),
            });
        } else {
            let f = File::open(&p)?;
            history_files.push(HistoryFile {
                reader: Box::new(BufReader::new(f)),
                path: Some(std::path::PathBuf::from(p)),
            });
        }
    }

    if format.is_none() {
        let detected = detect_format(history_files.iter_mut())?;
        format = detected;
        if format.is_none() {
            eprintln!("could not detect history format; please specify --format");
            process::exit(1);
        }
    }

    let entries = parse_entries(history_files)?;

    if count {
        println!("{}", entries.len());
    } else {
        let mut stdout = io::stdout();
        write_entries(&mut stdout, entries, format.unwrap())?;
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
