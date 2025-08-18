use histutils::{Context, HistoryFile, ShellFormat, parse_entries_with_ctx, write_entries};
use std::env;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::process;

use std::io::Write;

fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();
    let config = match parse_args(&args[1..]) {
        Ok(config) => config,
        Err(ArgError(msg)) => {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, msg));
        }
    };

    if config.print_help {
        println!(
            "usage: histutils [--output FILE] [--output-format FORMAT] [--count] [--epoch EPOCH] [--version] [FILE...]"
        );
        return Ok(());
    }

    if config.print_version {
        println!("histutils {}", env!("CARGO_PKG_VERSION"));
        return Ok(());
    }

    let history_files: Vec<HistoryFile<Box<dyn BufRead>>> = config
        .paths
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

    let ctx = Context {
        epoch: config.epoch,
        ..Default::default()
    };
    let history = parse_entries_with_ctx(history_files, &ctx)?;

    if config.count {
        println!("{}", history.entries.len());
    } else {
        let detected_format = history.primary_format();
        let format = config.output_format.or(detected_format);
        if format.is_none() {
            eprintln!("usage: --output-format= required when multiple input formats are given");
            process::exit(1);
        }
        let fmt = format.unwrap();

        let mut writer: Box<dyn Write> = if let Some(path) = config.output {
            Box::new(File::create(path)?)
        } else {
            Box::new(io::stdout())
        };

        if let Err(err) = write_entries(&mut writer, history.entries, fmt) {
            let msg = err.to_string();
            if err.kind() == io::ErrorKind::InvalidData && msg == "entry missing required timestamp"
            {
                let now = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_secs();
                eprintln!(
                    "usage: --epoch={now} required when exporting timestampless entries to {}",
                    fmt.as_str()
                );
            } else {
                eprintln!("{msg}");
            }
            process::exit(1);
        }
    }

    Ok(())
}

#[derive(Debug)]
struct ArgError(String);

#[derive(Debug, Default)]
struct Config {
    output_format: Option<ShellFormat>,
    output: Option<String>,
    paths: Vec<String>,
    count: bool,
    epoch: Option<u64>,
    print_help: bool,
    print_version: bool,
}

fn parse_args(args: &[String]) -> Result<Config, ArgError> {
    let mut args = args.iter();
    let mut config = Config::default();

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                config.print_help = true;
            }
            "--version" | "-V" => {
                config.print_version = true;
            }
            "--count" | "-c" => {
                config.count = true;
            }
            "--output" | "-o" => {
                if let Some(path) = args.next() {
                    config.output = Some(path.clone());
                } else {
                    return Err(ArgError(format!("{arg} requires a value")));
                }
            }
            "--epoch" => {
                if let Some(epoch_str) = args.next() {
                    if let Ok(e) = epoch_str.parse::<u64>() {
                        config.epoch = Some(e);
                    } else {
                        return Err(ArgError(format!("invalid epoch value: {epoch_str}")));
                    }
                } else {
                    return Err(ArgError("--epoch requires a value".to_string()));
                }
            }
            "--output-format" => {
                if let Some(fmt) = args.next() {
                    config.output_format = if let Some(f) = parse_format_opt(fmt) {
                        Some(f)
                    } else {
                        return Err(ArgError(format!("unknown format: {fmt}")));
                    };
                } else {
                    return Err(ArgError("--output-format requires a value".to_string()));
                }
            }
            _ if arg.starts_with("--output-format=") => {
                let fmt = &arg["--output-format=".len()..];
                config.output_format = if let Some(f) = parse_format_opt(fmt) {
                    Some(f)
                } else {
                    return Err(ArgError(format!("unknown format: {fmt}")));
                };
            }
            _ if arg.starts_with("--epoch=") => {
                let epoch_str = &arg["--epoch=".len()..];
                if let Ok(e) = epoch_str.parse::<u64>() {
                    config.epoch = Some(e);
                } else {
                    return Err(ArgError(format!("invalid epoch value: {epoch_str}")));
                }
            }
            _ => {
                config.paths.push(arg.clone());
            }
        }
    }

    if config.paths.is_empty() {
        config.paths.push("-".to_string());
    }

    Ok(config)
}

fn parse_format_opt(s: &str) -> Option<ShellFormat> {
    match s {
        "sh" | "bash" => Some(ShellFormat::Sh),
        "zsh" => Some(ShellFormat::ZshExtended),
        "fish" => Some(ShellFormat::Fish),
        _ => None,
    }
}
