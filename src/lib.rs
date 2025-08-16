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
    Fish,
}

pub fn parse_reader<R: Read>(reader: R) -> io::Result<Vec<HistoryEntry>> {
    let mut entries = Vec::new();
    let buf_reader = io::BufReader::new(reader);
    let mut lines = buf_reader.lines().peekable();

    if let Some(Ok(first_line)) = lines.peek()
        && first_line.trim_start().starts_with("- cmd:")
    {
        while let Some(line_res) = lines.next() {
            let line = line_res?;
            if line.trim_start().starts_with("- cmd:")
                && let Some(entry) = parse_fish_entry(line, &mut lines)
            {
                entries.push(entry);
            }
        }
        return Ok(entries);
    }

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

fn unescape_fish(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            if let Some(next) = chars.next() {
                match next {
                    'n' => out.push('\n'),
                    '\\' => out.push('\\'),
                    other => {
                        out.push('\\');
                        out.push(other);
                    }
                }
            } else {
                out.push('\\');
            }
        } else {
            out.push(ch);
        }
    }
    out
}

fn parse_fish_entry<I>(
    first_line: String,
    lines: &mut std::iter::Peekable<I>,
) -> Option<HistoryEntry>
where
    I: Iterator<Item = io::Result<String>>,
{
    let command_raw = first_line.trim_start().strip_prefix("- cmd:")?.trim_start();
    let command = unescape_fish(command_raw);
    let mut timestamp: Option<i64> = None;
    let mut paths: Vec<String> = Vec::new();

    while let Some(peek_res) = lines.peek() {
        let peek_line = peek_res.as_ref().ok()?;
        let t = peek_line.trim_start();
        if t.starts_with("- cmd:") {
            break;
        }

        let line = lines.next().unwrap().ok()?;
        let t = line.trim_start();

        if let Some(rest) = t.strip_prefix("when:") {
            let ts_str = rest.trim_start();
            timestamp = ts_str.parse().ok();
        } else if t.starts_with("paths:") {
            while let Some(path_res) = lines.peek() {
                let path_line = path_res.as_ref().ok()?;
                let ps = path_line.trim_start();
                if ps.starts_with("- cmd:") {
                    break;
                } else if ps.starts_with("- ") {
                    let line = lines.next().unwrap().ok()?;
                    let ps = line.trim_start();
                    paths.push(unescape_fish(&ps[2..]));
                } else if ps.is_empty() {
                    let _ = lines.next();
                    break;
                } else {
                    break;
                }
            }
        } else if t.is_empty() {
            continue;
        }
    }

    let timestamp = timestamp?;
    Some(HistoryEntry {
        timestamp,
        duration: 0,
        command,
        paths,
    })
}

pub fn write_entries<W: Write, I: IntoIterator<Item = HistoryEntry>>(
    writer: &mut W,
    entries: I,
    format: ShellFormat,
) -> io::Result<()> {
    match format {
        ShellFormat::Sh => write_sh_format(writer, entries),
        ShellFormat::ZshExtended => write_zsh_format(writer, entries),
        ShellFormat::Fish => write_fish_format(writer, entries),
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

fn write_fish_format<W: Write, I: IntoIterator<Item = HistoryEntry>>(
    writer: &mut W,
    entries: I,
) -> io::Result<()> {
    for entry in entries {
        writeln!(writer, "- cmd: {}", escape_fish(&entry.command))?;
        writeln!(writer, "  when: {}", entry.timestamp)?;
        if !entry.paths.is_empty() {
            writeln!(writer, "  paths:")?;
            for p in entry.paths {
                writeln!(writer, "    - {}", escape_fish(&p))?;
            }
        }
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

fn escape_fish(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '\n' => out.push_str("\\n"),
            '\\' => out.push_str("\\\\"),
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

    #[test]
    fn parse_fish_entry_basic() {
        let input = "- cmd: cargo build\n  when: 1700000000\n";
        let reader = Cursor::new(input);
        let entries = parse_reader(reader).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].timestamp, 1700000000);
        assert_eq!(entries[0].command, "cargo build");
    }

    #[test]
    fn parse_fish_entry_with_paths() {
        let input =
            "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n";
        let reader = Cursor::new(input);
        let entries = parse_reader(reader).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].paths, vec!["~/Developer/histutils".to_string()]);
    }

    #[test]
    fn parse_fish_entry_multiple_paths() {
        let input = "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/project1\n    - ~/project2\n";
        let reader = Cursor::new(input);
        let entries = parse_reader(reader).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(
            entries[0].paths,
            vec!["~/project1".to_string(), "~/project2".to_string()]
        );
    }

    #[test]
    fn parse_fish_multiline_command() {
        let input = "- cmd: echo \"hello\\nmultiline\\nstring\"\n  when: 1700000000\n";
        let reader = Cursor::new(input);
        let entries = parse_reader(reader).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "echo \"hello\nmultiline\nstring\"");
    }

    #[test]
    fn parse_fish_colon_in_command() {
        let input = "- cmd: git commit -m \"Test: something\"\n  when: 1516464765\n";
        let reader = Cursor::new(input);
        let entries = parse_reader(reader).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].timestamp, 1516464765);
        assert_eq!(entries[0].command, "git commit -m \"Test: something\"");
    }

    #[test]
    fn write_fish_entries() {
        let entries = vec![HistoryEntry {
            timestamp: 1700000000,
            duration: 0,
            command: "cargo build".to_string(),
            paths: vec!["~/Developer/histutils".to_string()],
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).expect("should write");

        let result = String::from_utf8(output).expect("valid utf8");
        let expected =
            "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n";
        assert_eq!(result, expected);
    }

    #[test]
    fn roundtrip_fish_multiline() {
        let original =
            "- cmd: echo hello\\nworld\n  when: 1700000001\n- cmd: ls\n  when: 1700000002\n";
        let reader = Cursor::new(original);
        let entries = parse_reader(reader).expect("should parse");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).expect("should write");
        let result = String::from_utf8(output).expect("valid utf8");

        assert_eq!(result, original);
    }

    #[test]
    fn roundtrip_fish_with_paths() {
        let original = "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n- cmd: ls\n  when: 1700000001\n";
        let reader = Cursor::new(original);
        let entries = parse_reader(reader).expect("should parse");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).expect("should write");
        let result = String::from_utf8(output).expect("valid utf8");

        assert_eq!(result, original);
    }

    #[test]
    fn parse_reader_ignores_invalid_and_empty() {
        let input = ": invalid\n\n";
        let reader = Cursor::new(input);
        let entries = parse_reader(reader).expect("should parse");
        assert!(entries.is_empty());
    }

    #[test]
    fn parse_fish_entry_handles_escapes() {
        let input = "- cmd: first\\nsecond\\\\third\\x\n  when: 1700000000\n";
        let reader = Cursor::new(input);
        let entries = parse_reader(reader).expect("should parse");
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "first\nsecond\\third\\x");
    }

    #[test]
    fn write_fish_escapes_special_chars() {
        let entries = vec![HistoryEntry {
            timestamp: 0,
            duration: 0,
            command: "one\ntwo\\".to_string(),
            paths: Vec::new(),
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).expect("should write");
        let result = String::from_utf8(output).expect("valid utf8");
        assert_eq!(result, "- cmd: one\\ntwo\\\\\n  when: 0\n");
    }

    #[test]
    fn write_bash_multiline_entry() {
        let entries = vec![HistoryEntry {
            timestamp: 0,
            duration: 0,
            command: "echo hello\nworld".to_string(),
            paths: Vec::new(),
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Sh).expect("should write");
        let result = String::from_utf8(output).expect("valid utf8");

        assert_eq!(result, "echo hello\\\nworld\n");
    }
}
