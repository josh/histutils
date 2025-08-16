use std::io::{self, BufRead, Read, Write};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HistoryEntry {
    pub timestamp: i64,
    pub duration: i64,
    pub command: String,
    pub paths: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShellFormat {
    Sh,
    ZshExtended,
}

pub fn parse_reader<R: Read>(reader: R) -> io::Result<Vec<HistoryEntry>> {
    let mut entries = Vec::new();
    let buf_reader = io::BufReader::new(reader);
    let mut lines = buf_reader.lines();

    while let Some(line_res) = lines.next() {
        let mut line = line_res?;

        while line.ends_with('\\') {
            line.pop();
            line.push('\n');

            if let Some(next_line_res) = lines.next() {
                let next_line = next_line_res?;
                line.push_str(&next_line);
            } else {
                break;
            }
        }

        if let Some(entry) = parse_line(&line) {
            entries.push(entry);
        }
    }
    Ok(entries)
}

fn parse_line(line: &str) -> Option<HistoryEntry> {
    let s = line.trim_start();

    if let Some(rest) = s.strip_prefix(':') {
        let mut rest = rest.trim_start();

        let idx_colon = rest.find(':')?;
        let ts_str = &rest[..idx_colon];
        rest = &rest[idx_colon + 1..];

        let idx_sc = rest.find(';')?;
        let dur_str = &rest[..idx_sc];
        let cmd_str = &rest[idx_sc + 1..];

        let timestamp: i64 = ts_str.parse().ok()?;
        let duration: i64 = dur_str.parse().ok()?;
        let command = cmd_str.to_string();

        Some(HistoryEntry {
            timestamp,
            duration,
            command,
            paths: Vec::new(),
        })
    } else if !s.is_empty() {
        let command = s.to_string();
        Some(HistoryEntry {
            timestamp: 0,
            duration: 0,
            command,
            paths: Vec::new(),
        })
    } else {
        None
    }
}

pub fn write_entries<W: Write, I: IntoIterator<Item = HistoryEntry>>(
    writer: &mut W,
    entries: I,
    format: ShellFormat,
) -> io::Result<()> {
    match format {
        ShellFormat::Sh => write_sh_format(writer, entries),
        ShellFormat::ZshExtended => write_zsh_format(writer, entries),
    }
}

fn write_sh_format<W: Write, I: IntoIterator<Item = HistoryEntry>>(
    writer: &mut W,
    entries: I,
) -> io::Result<()> {
    for entry in entries {
        writeln!(writer, "{}", escape_command(&entry.command))?;
    }
    Ok(())
}

fn write_zsh_format<W: Write, I: IntoIterator<Item = HistoryEntry>>(
    writer: &mut W,
    entries: I,
) -> io::Result<()> {
    for entry in entries {
        writeln!(
            writer,
            ": {}:{};{}",
            entry.timestamp,
            entry.duration,
            escape_command(&entry.command)
        )?;
    }
    Ok(())
}

fn escape_command(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '\n' => out.push_str("\\\n"),
            _ => out.push(ch),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn parse_simple_entry() {
        let input = "echo hello\n";
        let reader = Cursor::new(input);
        let entries = parse_reader(reader).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "echo hello");
    }

    #[test]
    fn parse_simple_entries() {
        let input = "echo hello\nls -la\npwd\n";
        let reader = Cursor::new(input);
        let entries = parse_reader(reader).expect("should parse");

        assert_eq!(entries.len(), 3);
        assert_eq!(entries[0].command, "echo hello");
        assert_eq!(entries[1].command, "ls -la");
        assert_eq!(entries[2].command, "pwd");
    }

    #[test]
    fn parse_simple_multiline_entry() {
        let input = "echo hello\\\nanother\\\nline\n";
        let reader = Cursor::new(input);
        let entries = parse_reader(reader).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "echo hello\nanother\nline");
    }

    #[test]
    fn parse_extended_entries() {
        let input = ": 1700000001:0;echo hello\n: 1700000002:5;ls -la\n";
        let reader = Cursor::new(input);
        let entries = parse_reader(reader).expect("should parse");

        assert_eq!(entries.len(), 2);

        assert_eq!(entries[0].timestamp, 1700000001);
        assert_eq!(entries[0].duration, 0);
        assert_eq!(entries[0].command, "echo hello");

        assert_eq!(entries[1].timestamp, 1700000002);
        assert_eq!(entries[1].duration, 5);
        assert_eq!(entries[1].command, "ls -la");
    }

    #[test]
    fn write_simple_entries_bash() {
        let entries = vec![
            HistoryEntry {
                timestamp: 0,
                duration: 0,
                command: "echo hello".to_string(),
                paths: Vec::new(),
            },
            HistoryEntry {
                timestamp: 0,
                duration: 0,
                command: "ls -la".to_string(),
                paths: Vec::new(),
            },
        ];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Sh).expect("should write");

        let result = String::from_utf8(output).expect("should be valid utf8");
        assert_eq!(result, "echo hello\nls -la\n");
    }

    #[test]
    fn write_extended_entries_zsh() {
        let entries = vec![
            HistoryEntry {
                timestamp: 1700000001,
                duration: 0,
                command: "echo hello".to_string(),
                paths: Vec::new(),
            },
            HistoryEntry {
                timestamp: 1700000002,
                duration: 5,
                command: "ls -la".to_string(),
                paths: Vec::new(),
            },
        ];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::ZshExtended).expect("should write");

        let result = String::from_utf8(output).expect("should be valid utf8");
        assert_eq!(result, ": 1700000001:0;echo hello\n: 1700000002:5;ls -la\n");
    }

    #[test]
    fn write_multiline_entry_zsh() {
        let entries = vec![HistoryEntry {
            timestamp: 1700000001,
            duration: 0,
            command: "echo hello\nworld".to_string(),
            paths: Vec::new(),
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::ZshExtended).expect("should write");

        let result = String::from_utf8(output).expect("should be valid utf8");
        assert_eq!(result, ": 1700000001:0;echo hello\\\nworld\n");
    }

    #[test]
    fn roundtrip_zsh_multiline() {
        let original = ": 1700000001:0;echo hello\\\nworld\n: 1700000002:5;ls -la\n";

        let reader = Cursor::new(original);
        let entries = parse_reader(reader).expect("should parse");

        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].command, "echo hello\nworld");
        assert_eq!(entries[1].command, "ls -la");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::ZshExtended).expect("should write");
        let result = String::from_utf8(output).expect("should be valid utf8");

        assert_eq!(result, original);
    }
}
