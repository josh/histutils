use histutils::{Context, HistoryFile, ShellFormat, parse_entries_with_ctx, write_entries};
use std::env;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};
use std::process;

fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();
    let config = match parse_args(&args[1..]) {
        Ok(config) => config,
        Err(ArgError(msg)) => {
            eprintln!("{msg}");
            std::process::exit(1);
        }
    };

    if let Some(action) = config.action {
        match action {
            ConfigAction::PrintHelp => {
                println!(
                    "usage: histutils [--output FILE] [--output-format FORMAT] [--head N] [--tail N] [--count] [--fix] [--version] [FILE...]"
                );
            }
            ConfigAction::PrintVersion => {
                println!("histutils {}", env!("CARGO_PKG_VERSION"));
            }
        }
        return Ok(());
    }

    let history_files: Vec<HistoryFile<InputReader>> = config
        .paths
        .into_iter()
        .map(|p| -> io::Result<HistoryFile<InputReader>> {
            if p == "-" {
                Ok(HistoryFile {
                    reader: InputReader::Stdin(BufReader::new(io::stdin())),
                    path: None,
                })
            } else {
                let f = File::open(&p)?;
                Ok(HistoryFile {
                    reader: InputReader::File(BufReader::new(f)),
                    path: Some(std::path::PathBuf::from(p)),
                })
            }
        })
        .collect::<io::Result<Vec<_>>>()?;

    let ctx = Context {
        fix: config.fix,
        ..Context::default()
    };
    let mut history = parse_entries_with_ctx(history_files, &ctx)?;

    if let Some(limit) = config.head {
        if history.entries.len() > limit {
            history.entries.truncate(limit);
        }
    } else if let Some(limit) = config.tail {
        let len = history.entries.len();
        if limit < len {
            history.entries.drain(0..len - limit);
        }
    }

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

        if matches!(fmt, ShellFormat::ZshExtended | ShellFormat::Fish) {
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs();
            let mut warned = false;
            for entry in &mut history.entries {
                if entry.timestamp.is_none() {
                    entry.timestamp = Some(now);
                    warned = true;
                }
            }
            if warned {
                eprintln!(
                    "warning: setting timestamp on entries without one; duplicates may be merged"
                );
            }
        }

        let mut writers = Vec::with_capacity(config.outputs.len());
        for path in &config.outputs {
            if path == "-" {
                writers.push(OutputWriter::Stdout(io::stdout()));
            } else {
                writers.push(OutputWriter::File(File::create(path)?));
            }
        }

        for writer in &mut writers {
            if let Err(err) = write_entries(writer, history.entries.iter().cloned(), fmt) {
                eprintln!("{err}");
                process::exit(1);
            }
        }
    }

    Ok(())
}

#[derive(Debug)]
struct ArgError(String);

#[derive(Debug, Default)]
struct Config {
    output_format: Option<ShellFormat>,
    outputs: Vec<String>,
    paths: Vec<String>,
    head: Option<usize>,
    tail: Option<usize>,
    count: bool,
    fix: bool,
    action: Option<ConfigAction>,
}

#[derive(Debug, Clone, Copy)]
enum ConfigAction {
    PrintHelp,
    PrintVersion,
}

fn parse_args(args: &[String]) -> Result<Config, ArgError> {
    let mut args = args.iter();
    let mut config = Config::default();

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                if config.action.is_some() {
                    return Err(ArgError(
                        "usage: --help and --version are mutually exclusive".to_string(),
                    ));
                }
                config.action = Some(ConfigAction::PrintHelp);
            }
            "--version" | "-V" => {
                if config.action.is_some() {
                    return Err(ArgError(
                        "usage: --help and --version are mutually exclusive".to_string(),
                    ));
                }
                config.action = Some(ConfigAction::PrintVersion);
            }
            "--count" | "-c" => {
                if config.count {
                    return Err(ArgError(
                        "usage: --count specified multiple times".to_string(),
                    ));
                }
                config.count = true;
            }
            "--fix" => {
                if config.fix {
                    return Err(ArgError(
                        "usage: --fix specified multiple times".to_string(),
                    ));
                }
                config.fix = true;
            }
            "--head" | "--tail" => {
                let Some(value) = args.next() else {
                    return Err(ArgError(format!("{arg} requires a value")));
                };
                set_limit(&mut config, arg, value.as_str())?;
            }
            "--output" | "-o" => {
                if let Some(path) = args.next() {
                    config.outputs.push(path.clone());
                } else {
                    return Err(ArgError(format!("{arg} requires a value")));
                }
            }
            "--output-format" => {
                if config.output_format.is_some() {
                    return Err(ArgError(
                        "usage: --output-format specified multiple times".to_string(),
                    ));
                }
                if let Some(fmt) = args.next() {
                    config.output_format = if let Some(f) = parse_format_opt(fmt) {
                        Some(f)
                    } else {
                        return Err(ArgError(format!("usage: unknown --output-format={fmt}")));
                    };
                } else {
                    return Err(ArgError("--output-format requires a value".to_string()));
                }
            }
            _ if arg.starts_with("--output-format=") => {
                if config.output_format.is_some() {
                    return Err(ArgError(
                        "usage: --output-format specified multiple times".to_string(),
                    ));
                }
                let fmt = &arg["--output-format=".len()..];
                config.output_format = if let Some(f) = parse_format_opt(fmt) {
                    Some(f)
                } else {
                    return Err(ArgError(format!("usage: unknown --output-format={fmt}")));
                };
            }
            _ if arg.starts_with("--head=") || arg.starts_with("--tail=") => {
                let (flag, value) = arg.split_once('=').expect("split on '='");
                set_limit(&mut config, flag, value)?;
            }
            _ => {
                config.paths.push(arg.clone());
            }
        }
    }

    if config.outputs.is_empty() {
        config.outputs.push("-".to_string());
    }

    if config.paths.is_empty() {
        config.paths.push("-".to_string());
    }

    Ok(config)
}

fn parse_format_opt(s: &str) -> Option<ShellFormat> {
    match s {
        "sh" | "bash" => Some(ShellFormat::Sh),
        "zsh" | "zsh-extended" => Some(ShellFormat::ZshExtended),
        "fish" => Some(ShellFormat::Fish),
        _ => None,
    }
}

fn set_limit(config: &mut Config, flag: &str, value: &str) -> Result<(), ArgError> {
    match flag {
        "--head" => {
            if config.head.is_some() {
                return Err(ArgError(
                    "usage: --head specified multiple times".to_string(),
                ));
            }
            if config.tail.is_some() {
                return Err(ArgError(
                    "usage: --head cannot be used with --tail".to_string(),
                ));
            }
            config.head = Some(parse_limit(value, flag)?);
        }
        "--tail" => {
            if config.tail.is_some() {
                return Err(ArgError(
                    "usage: --tail specified multiple times".to_string(),
                ));
            }
            if config.head.is_some() {
                return Err(ArgError(
                    "usage: --tail cannot be used with --head".to_string(),
                ));
            }
            config.tail = Some(parse_limit(value, flag)?);
        }
        _ => unreachable!("unexpected flag"),
    }

    Ok(())
}

fn parse_limit(value: &str, flag: &str) -> Result<usize, ArgError> {
    value
        .parse::<usize>()
        .map_err(|_| ArgError(format!("usage: invalid {flag} value '{value}'")))
}

enum InputReader {
    Stdin(BufReader<io::Stdin>),
    File(BufReader<File>),
}

impl io::Read for InputReader {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            InputReader::Stdin(reader) => reader.read(buf),
            InputReader::File(reader) => reader.read(buf),
        }
    }
}

impl BufRead for InputReader {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        match self {
            InputReader::Stdin(reader) => reader.fill_buf(),
            InputReader::File(reader) => reader.fill_buf(),
        }
    }

    fn consume(&mut self, amt: usize) {
        match self {
            InputReader::Stdin(reader) => reader.consume(amt),
            InputReader::File(reader) => reader.consume(amt),
        }
    }

    fn read_until(&mut self, byte: u8, buf: &mut Vec<u8>) -> io::Result<usize> {
        match self {
            InputReader::Stdin(reader) => reader.read_until(byte, buf),
            InputReader::File(reader) => reader.read_until(byte, buf),
        }
    }

    fn read_line(&mut self, buf: &mut String) -> io::Result<usize> {
        match self {
            InputReader::Stdin(reader) => reader.read_line(buf),
            InputReader::File(reader) => reader.read_line(buf),
        }
    }
}

enum OutputWriter {
    Stdout(io::Stdout),
    File(File),
}

impl Write for OutputWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            OutputWriter::Stdout(stdout) => stdout.write(buf),
            OutputWriter::File(file) => file.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            OutputWriter::Stdout(stdout) => stdout.flush(),
            OutputWriter::File(file) => file.flush(),
        }
    }
}
