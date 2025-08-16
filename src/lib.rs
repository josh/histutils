use std::collections::BTreeMap;
use std::io::{self, BufRead, Read, Write};
use std::path::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HistoryEntry {
    pub timestamp: u64,
    pub duration: u64,
    pub command: String,
    pub paths: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShellFormat {
    Sh,
    ZshExtended,
    Fish,
}

/// Detects the history format of one or more readers.
///
/// Returns `Some(ShellFormat)` if all readers appear to be in the same
/// format. If readers of different formats are provided or no format can be
/// detected, `None` is returned.
///
/// # Arguments
///
/// * `readers` - An iterator of mutable references to readers that implement
///   `Read + Seek`. The readers will be read from and then reset to the
///   beginning position.
///
/// # Examples
///
/// ```
/// let r1 = std::io::Cursor::new(": 1:0;echo hello\n");
/// let r2 = std::io::Cursor::new(": 2:0;ls -la\n");
/// let mut readers = [r1, r2];
/// let format = histutils::detect_format(readers.iter_mut()).unwrap();
/// assert_eq!(format, Some(histutils::ShellFormat::ZshExtended));
/// ```
///
/// # Errors
///
/// Returns any I/O error encountered while reading from the inputs.
pub fn detect_format<'a, R, I>(readers: I) -> io::Result<Option<ShellFormat>>
where
    R: Read + io::Seek + 'a + ?Sized,
    I: Iterator<Item = &'a mut R>,
{
    let mut detected: Option<ShellFormat> = None;
    for reader in readers {
        let mut buf_reader = io::BufReader::new(reader);
        let mut line = Vec::new();
        let bytes = buf_reader.read_until(b'\n', &mut line)?;
        buf_reader.into_inner().seek(io::SeekFrom::Start(0))?;
        if bytes == 0 {
            continue;
        }
        let fmt = detect_format_line(&line);
        if let Some(existing) = detected {
            if existing != fmt {
                return Ok(None);
            }
        } else {
            detected = Some(fmt);
        }
    }
    Ok(detected)
}

/// Parses and merges history entries from multiple readers.
///
/// This function reads shell history from multiple sources, parses the entries,
/// and merges them into a single timestamp sorted collection.
///
/// # Arguments
///
/// * `readers` - An iterator of tuples containing a reader and its associated
///   path. The reader must implement `Read` and the path must implement
///   `AsRef<Path>`. The path is used for error reporting and format detection.
///
/// # Examples
///
/// ```
/// let zsh_history = std::io::Cursor::new(": 1609459200:5;echo hello\n: 1609459300:2;ls -la\n");
/// let fish_history = std::io::Cursor::new("- cmd: pwd\n  when: 1609459250\n");
///
/// let readers = [
///     (zsh_history, std::path::Path::new("~/.zsh_history")),
///     (fish_history, std::path::Path::new("~/.local/share/fish/fish_history")),
/// ];
///
/// let entries = histutils::parse_entries(readers).unwrap();
/// assert_eq!(entries.len(), 3);
/// ```
///
/// # Errors
///
/// Returns an error if reading from any reader fails.
pub fn parse_entries<R, P, I>(readers: I) -> io::Result<Vec<HistoryEntry>>
where
    R: Read,
    P: AsRef<Path>,
    I: IntoIterator<Item = (R, P)>,
{
    let mut map: BTreeMap<u64, Vec<HistoryEntry>> = BTreeMap::new();
    for (reader, path) in readers {
        for entry in parse_reader(reader, path)? {
            let entries = map.entry(entry.timestamp).or_default();
            if entry.timestamp == 0 {
                entries.push(entry);
                continue;
            }
            if let Some(existing) = entries.iter_mut().find(|e| e.command == entry.command) {
                let merged = merge_entries(existing.clone(), entry);
                *existing = merged;
            } else {
                entries.push(entry);
            }
        }
    }
    Ok(map.into_iter().flat_map(|(_, v)| v).collect())
}

fn merge_entries(mut a: HistoryEntry, b: HistoryEntry) -> HistoryEntry {
    debug_assert!(
        a.duration == b.duration || a.duration == 0 || b.duration == 0,
        "merging entries with conflicting durations",
    );
    if a.duration == 0 {
        a.duration = b.duration;
    }
    if a.paths.is_empty() {
        a.paths = b.paths;
    } else if !b.paths.is_empty() {
        for p in b.paths {
            if !a.paths.contains(&p) {
                a.paths.push(p);
            }
        }
    }
    a
}

fn detect_format_line(first_line: &[u8]) -> ShellFormat {
    let first_line = trim_start(first_line);
    if first_line.starts_with(b"- cmd:") {
        ShellFormat::Fish
    } else if first_line.starts_with(b":") {
        ShellFormat::ZshExtended
    } else {
        ShellFormat::Sh
    }
}

fn detect_format_from_lines<I>(lines: &mut std::iter::Peekable<I>) -> ShellFormat
where
    I: Iterator<Item = io::Result<Vec<u8>>>,
{
    if let Some(Ok(first_line)) = lines.peek() {
        detect_format_line(first_line)
    } else {
        ShellFormat::Sh
    }
}

fn parse_sh_format<I>(
    lines: &mut std::iter::Peekable<I>,
    path: Option<&Path>,
) -> io::Result<Vec<HistoryEntry>>
where
    I: Iterator<Item = io::Result<Vec<u8>>>,
{
    let mut entries = Vec::new();
    let mut line_no: usize = 0;

    while let Some(line_res) = lines.next() {
        line_no += 1;
        let mut line = line_res?;
        let start_line = line_no;

        while line.ends_with(b"\\") {
            line.pop();
            line.push(b'\n');

            if let Some(next_line_res) = lines.next() {
                line_no += 1;
                let next_line = next_line_res?;
                line.extend_from_slice(&next_line);
            } else {
                break;
            }
        }

        match parse_sh_line_bytes(&line) {
            Some((entry, invalid)) => {
                if invalid {
                    warn_lossy_utf8(path, start_line, "command", &line);
                }
                entries.push(entry);
            }
            None if !trim_start(&line).is_empty() => warn_invalid(path, start_line, &line),
            None => {}
        }
    }

    Ok(entries)
}

fn parse_zsh_extended_format<I>(
    lines: &mut std::iter::Peekable<I>,
    path: Option<&Path>,
) -> io::Result<Vec<HistoryEntry>>
where
    I: Iterator<Item = io::Result<Vec<u8>>>,
{
    let mut entries = Vec::new();
    let mut line_no: usize = 0;

    while let Some(line_res) = lines.next() {
        line_no += 1;
        let mut line = line_res?;
        let start_line = line_no;

        while line.ends_with(b"\\") {
            line.pop();
            line.push(b'\n');

            if let Some(next_line_res) = lines.next() {
                line_no += 1;
                let next_line = next_line_res?;
                line.extend_from_slice(&next_line);
            } else {
                break;
            }
        }

        match parse_zsh_extended_line_bytes(&line) {
            Ok(Some((entry, invalid))) => {
                if invalid {
                    warn_lossy_utf8(path, start_line, "command", &line);
                }
                entries.push(entry);
            }
            Ok(None) => {
                if !trim_start(&line).is_empty() {
                    warn_invalid(path, start_line, &line);
                }
            }
            Err(LineParseError::InvalidUtf8) => {
                return Err(invalid_utf8_error(path, start_line));
            }
        }
    }

    Ok(entries)
}

fn parse_fish_format<I>(
    lines: &mut std::iter::Peekable<I>,
    path: Option<&Path>,
) -> io::Result<Vec<HistoryEntry>>
where
    I: Iterator<Item = io::Result<Vec<u8>>>,
{
    let mut entries = Vec::new();
    let mut line_no: usize = 0;

    while let Some(line_res) = lines.next() {
        line_no += 1;
        let line = line_res?;
        let t = trim_start(&line);
        if t.starts_with(b"- cmd:") {
            let start_line = line_no;
            match parse_fish_entry_bytes(&line, lines, &mut line_no, path, start_line) {
                Ok(Some(entry)) => entries.push(entry),
                Ok(None) => warn_invalid(path, start_line, &line),
                Err(LineParseError::InvalidUtf8) => {
                    return Err(invalid_utf8_error(path, start_line));
                }
            }
        } else if !t.is_empty() {
            warn_invalid(path, line_no, &line);
        }
    }

    Ok(entries)
}

struct ByteLines<R: BufRead> {
    reader: R,
    buf: Vec<u8>,
}

impl<R: BufRead> ByteLines<R> {
    fn new(reader: R) -> Self {
        Self {
            reader,
            buf: Vec::new(),
        }
    }
}

impl<R: BufRead> Iterator for ByteLines<R> {
    type Item = io::Result<Vec<u8>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.buf.clear();
        match self.reader.read_until(b'\n', &mut self.buf) {
            Ok(0) => None,
            Ok(_) => {
                if self.buf.ends_with(b"\n") {
                    self.buf.pop();
                    if self.buf.ends_with(b"\r") {
                        self.buf.pop();
                    }
                }
                Some(Ok(self.buf.clone()))
            }
            Err(e) => Some(Err(e)),
        }
    }
}

fn parse_reader<R: Read, P: AsRef<Path>>(reader: R, path: P) -> io::Result<Vec<HistoryEntry>> {
    let buf_reader = io::BufReader::new(reader);
    let mut lines = ByteLines::new(buf_reader).peekable();
    let path = path.as_ref();

    match detect_format_from_lines(&mut lines) {
        ShellFormat::Fish => parse_fish_format(&mut lines, Some(path)),
        ShellFormat::ZshExtended => parse_zsh_extended_format(&mut lines, Some(path)),
        ShellFormat::Sh => parse_sh_format(&mut lines, Some(path)),
    }
}

fn warn_invalid(path: Option<&Path>, line_no: usize, line: &[u8]) {
    let display = String::from_utf8_lossy(line);
    if let Some(p) = path {
        eprintln!(
            "warning: invalid history entry in {}:{line_no}: {display}",
            p.display(),
        );
    } else {
        eprintln!("warning: invalid history entry at line {line_no}: {display}");
    }
}

fn warn_lossy_utf8(path: Option<&Path>, line_no: usize, what: &str, line: &[u8]) {
    let display = String::from_utf8_lossy(line);
    if let Some(p) = path {
        println!(
            "warning: invalid UTF-8 in {what} in {}:{line_no}: {display}",
            p.display(),
        );
    } else {
        println!("warning: invalid UTF-8 in {what} at line {line_no}: {display}");
    }
}

fn invalid_utf8_error(path: Option<&Path>, line_no: usize) -> io::Error {
    if let Some(p) = path {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("invalid UTF-8 in metadata in {}:{line_no}", p.display()),
        )
    } else {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("invalid UTF-8 in metadata at line {line_no}"),
        )
    }
}

enum LineParseError {
    InvalidUtf8,
}

fn trim_start(mut s: &[u8]) -> &[u8] {
    while let Some((&b, rest)) = s.split_first() {
        if b == b' ' || b == b'\t' {
            s = rest;
        } else {
            break;
        }
    }
    s
}

fn strip_prefix<'a>(s: &'a [u8], prefix: &[u8]) -> Option<&'a [u8]> {
    if s.starts_with(prefix) {
        Some(&s[prefix.len()..])
    } else {
        None
    }
}

fn decode_lossy(bytes: &[u8]) -> (String, bool) {
    match std::str::from_utf8(bytes) {
        Ok(s) => (s.to_string(), false),
        Err(_) => (String::from_utf8_lossy(bytes).into_owned(), true),
    }
}

fn parse_zsh_extended_line_bytes(
    line: &[u8],
) -> Result<Option<(HistoryEntry, bool)>, LineParseError> {
    let s = trim_start(line);
    if !s.starts_with(b":") {
        return Ok(None);
    }
    let rest = trim_start(&s[1..]);

    let Some(idx_colon) = rest.iter().position(|&b| b == b':') else {
        return Ok(None);
    };
    let ts_bytes = &rest[..idx_colon];
    let rest = &rest[idx_colon + 1..];

    let Some(idx_sc) = rest.iter().position(|&b| b == b';') else {
        return Ok(None);
    };
    let dur_bytes = &rest[..idx_sc];
    let cmd_bytes = &rest[idx_sc + 1..];

    let ts_str = std::str::from_utf8(ts_bytes).map_err(|_| LineParseError::InvalidUtf8)?;
    let dur_str = std::str::from_utf8(dur_bytes).map_err(|_| LineParseError::InvalidUtf8)?;
    let timestamp: u64 = match ts_str.parse() {
        Ok(t) => t,
        Err(_) => return Ok(None),
    };
    let duration: u64 = match dur_str.parse() {
        Ok(d) => d,
        Err(_) => return Ok(None),
    };

    let (command, invalid) = decode_lossy(cmd_bytes);

    Ok(Some((
        HistoryEntry {
            timestamp,
            duration,
            command,
            paths: Vec::new(),
        },
        invalid,
    )))
}

fn parse_sh_line_bytes(line: &[u8]) -> Option<(HistoryEntry, bool)> {
    let s = trim_start(line);
    if s.is_empty() || s.starts_with(b":") {
        return None;
    }
    let (command, invalid) = decode_lossy(s);
    Some((
        HistoryEntry {
            timestamp: 0,
            duration: 0,
            command,
            paths: Vec::new(),
        },
        invalid,
    ))
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

fn parse_fish_entry_bytes<I>(
    first_line: &[u8],
    lines: &mut std::iter::Peekable<I>,
    line_no: &mut usize,
    path: Option<&Path>,
    start_line: usize,
) -> Result<Option<HistoryEntry>, LineParseError>
where
    I: Iterator<Item = io::Result<Vec<u8>>>,
{
    let t = trim_start(first_line);
    let Some(cmd_bytes) = strip_prefix(t, b"- cmd:") else {
        return Ok(None);
    };
    let cmd_bytes = trim_start(cmd_bytes);
    let (cmd_raw, invalid_cmd) = decode_lossy(cmd_bytes);
    if invalid_cmd {
        warn_lossy_utf8(path, start_line, "command", first_line);
    }
    let command = unescape_fish(&cmd_raw);
    let mut timestamp: Option<u64> = None;
    let mut paths: Vec<String> = Vec::new();

    while let Some(peek_res) = lines.peek() {
        let peek_line = peek_res.as_ref().map_err(|_| LineParseError::InvalidUtf8)?;
        let t = trim_start(peek_line);
        if t.starts_with(b"- cmd:") {
            break;
        }

        let line = lines
            .next()
            .unwrap()
            .map_err(|_| LineParseError::InvalidUtf8)?;
        *line_no += 1;
        let t = trim_start(&line);

        if let Some(rest) = strip_prefix(t, b"when:") {
            let ts_bytes = trim_start(rest);
            let ts_str = std::str::from_utf8(ts_bytes).map_err(|_| LineParseError::InvalidUtf8)?;
            timestamp = match ts_str.parse() {
                Ok(t) => Some(t),
                Err(_) => return Ok(None),
            };
        } else if t.starts_with(b"paths:") {
            while let Some(path_res) = lines.peek() {
                let path_line = path_res.as_ref().map_err(|_| LineParseError::InvalidUtf8)?;
                let ps = trim_start(path_line);
                if ps.starts_with(b"- cmd:") {
                    break;
                } else if ps.starts_with(b"- ") {
                    let line = lines
                        .next()
                        .unwrap()
                        .map_err(|_| LineParseError::InvalidUtf8)?;
                    *line_no += 1;
                    let ps = trim_start(&line);
                    let path_bytes = &ps[2..];
                    let (p_raw, invalid) = decode_lossy(path_bytes);
                    if invalid {
                        warn_lossy_utf8(path, *line_no, "path", &line);
                    }
                    paths.push(unescape_fish(&p_raw));
                } else if ps.is_empty() {
                    let _ = lines.next();
                    *line_no += 1;
                    break;
                } else {
                    break;
                }
            }
        }
    }

    let Some(timestamp) = timestamp else {
        return Ok(None);
    };

    Ok(Some(HistoryEntry {
        timestamp,
        duration: 0,
        command,
        paths,
    }))
}

/// Writes history entries in the specified format.
///
/// # Errors
///
/// Returns an error if writing to the output fails.
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
    use std::io::{self, Cursor};

    #[test]
    fn detect_format_none() {
        let mut readers: Vec<std::io::Cursor<&[u8]>> = Vec::new();
        let fmt = detect_format(readers.iter_mut()).unwrap();
        assert_eq!(fmt, None);
    }

    #[test]
    fn detect_format_one_sh() {
        let reader = Cursor::new("echo hello\n");
        let mut readers = [reader];
        let fmt = detect_format(readers.iter_mut()).unwrap();
        assert_eq!(fmt, Some(ShellFormat::Sh));
    }

    #[test]
    fn detect_format_one_zsh() {
        let reader = Cursor::new(": 1:0;echo hello\n");
        let mut readers = [reader];
        let fmt = detect_format(readers.iter_mut()).unwrap();
        assert_eq!(fmt, Some(ShellFormat::ZshExtended));
    }

    #[test]
    fn detect_format_one_fish() {
        let reader = Cursor::new("- cmd: echo hello\n  when: 1\n");
        let mut readers = [reader];
        let fmt = detect_format(readers.iter_mut()).unwrap();
        assert_eq!(fmt, Some(ShellFormat::Fish));
    }

    #[test]
    fn detect_format_multiple_sh() {
        let r1 = Cursor::new("echo foo\n");
        let r2 = Cursor::new("echo bar\n");
        let r3 = Cursor::new("echo baz\n");
        let mut readers = [r1, r2, r3];
        let fmt = detect_format(readers.iter_mut()).unwrap();
        assert_eq!(fmt, Some(ShellFormat::Sh));
    }

    #[test]
    fn detect_format_multiple_zsh() {
        let r1 = Cursor::new(": 1:0;echo foo\n");
        let r2 = Cursor::new(": 2:0;echo bar\n");
        let r3 = Cursor::new(": 3:0;echo baz\n");
        let mut readers = [r1, r2, r3];
        let fmt = detect_format(readers.iter_mut()).unwrap();
        assert_eq!(fmt, Some(ShellFormat::ZshExtended));
    }

    #[test]
    fn detect_format_multiple_fish() {
        let r1 = Cursor::new("- cmd: echo foo\n  when: 1\n");
        let r2 = Cursor::new("- cmd: echo bar\n  when: 2\n");
        let r3 = Cursor::new("- cmd: echo baz\n  when: 3\n");
        let mut readers = [r1, r2, r3];
        let fmt = detect_format(readers.iter_mut()).unwrap();
        assert_eq!(fmt, Some(ShellFormat::Fish));
    }

    #[test]
    fn detect_format_mixed() {
        let zsh = Cursor::new(": 1:0;echo foo\n");
        let fish = Cursor::new("- cmd: echo bar\n  when: 2\n");
        let mut readers = [zsh, fish];
        let fmt = detect_format(readers.iter_mut()).unwrap();
        assert_eq!(fmt, None);
    }

    #[test]
    fn parse_simple_entry() {
        let input = "echo hello\n";
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "echo hello");
    }

    #[test]
    fn parse_simple_entries() {
        let input = "echo hello\nls -la\npwd\n";
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 3);
        assert_eq!(entries[0].command, "echo hello");
        assert_eq!(entries[1].command, "ls -la");
        assert_eq!(entries[2].command, "pwd");
    }

    #[test]
    fn parse_simple_multiline_entry() {
        let input = "echo hello\\\nanother\\\nline\n";
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "echo hello\nanother\nline");
    }

    #[test]
    fn roundtrip_sh_backslash() {
        let original = "echo foo \\ hello\n";
        let reader = Cursor::new(original);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, r"echo foo \ hello");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Sh).expect("should write");
        let result = String::from_utf8(output).expect("should be valid utf8");
        assert_eq!(result, original);
    }

    #[test]
    fn roundtrip_sh_multiline() {
        let original = "echo foo\\\nbar\\\nbaz\n";
        let reader = Cursor::new(original);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "echo foo\nbar\nbaz");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Sh).expect("should write");
        let result = String::from_utf8(output).expect("should be valid utf8");
        assert_eq!(result, original);
    }

    #[test]
    fn parse_extended_entries() {
        let input = ": 1700000001:0;echo hello\n: 1700000002:5;ls -la\n";
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 2);

        assert_eq!(entries[0].timestamp, 1_700_000_001);
        assert_eq!(entries[0].duration, 0);
        assert_eq!(entries[0].command, "echo hello");

        assert_eq!(entries[1].timestamp, 1_700_000_002);
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
                timestamp: 1_700_000_001,
                duration: 0,
                command: "echo hello".to_string(),
                paths: Vec::new(),
            },
            HistoryEntry {
                timestamp: 1_700_000_002,
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
            timestamp: 1_700_000_001,
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
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].command, "echo hello\nworld");
        assert_eq!(entries[1].command, "ls -la");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::ZshExtended).expect("should write");
        let result = String::from_utf8(output).expect("should be valid utf8");

        assert_eq!(result, original);
    }

    #[test]
    fn roundtrip_zsh_colon_continuation() {
        let original = ": 100:0;echo foo\\\n: 200:0;echo bar\n";
        let reader = Cursor::new(original);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].timestamp, 100);
        assert_eq!(entries[0].command, "echo foo\n: 200:0;echo bar");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::ZshExtended).expect("should write");
        let result = String::from_utf8(output).expect("should be valid utf8");
        assert_eq!(result, original);
    }

    #[test]
    fn parse_fish_entry_basic() {
        let input = "- cmd: cargo build\n  when: 1700000000\n";
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].timestamp, 1_700_000_000);
        assert_eq!(entries[0].command, "cargo build");
    }

    #[test]
    fn parse_fish_entry_with_paths() {
        let input =
            "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n";
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].paths, vec!["~/Developer/histutils".to_string()]);
    }

    #[test]
    fn parse_fish_entry_multiple_paths() {
        let input = "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/project1\n    - ~/project2\n";
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(
            entries[0].paths,
            vec!["~/project1".to_string(), "~/project2".to_string()]
        );
    }

    #[test]
    fn parse_fish_entry_paths_then_new_entry() {
        let input = "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/project1\n- cmd: echo hi\n  when: 1700000001\n";
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].paths, vec!["~/project1".to_string()]);
        assert_eq!(entries[1].command, "echo hi");
    }

    #[test]
    fn parse_fish_multiline_command() {
        let input = "- cmd: echo \"hello\\nmultiline\\nstring\"\n  when: 1700000000\n";
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "echo \"hello\nmultiline\nstring\"");
    }

    #[test]
    fn parse_fish_colon_in_command() {
        let input = "- cmd: git commit -m \"Test: something\"\n  when: 1516464765\n";
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].timestamp, 1_516_464_765);
        assert_eq!(entries[0].command, "git commit -m \"Test: something\"");
    }

    #[test]
    fn write_fish_entries() {
        let entries = vec![HistoryEntry {
            timestamp: 1_700_000_000,
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
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).expect("should write");
        let result = String::from_utf8(output).expect("valid utf8");

        assert_eq!(result, original);
    }

    #[test]
    fn roundtrip_fish_with_paths() {
        let original = "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n- cmd: ls\n  when: 1700000001\n";
        let reader = Cursor::new(original);
        let entries = parse_entries([(reader, "-")]).expect("should parse");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).expect("should write");
        let result = String::from_utf8(output).expect("valid utf8");

        assert_eq!(result, original);
    }

    #[test]
    fn parse_reader_ignores_invalid_and_empty() {
        let input = ": invalid\n\n";
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");
        assert!(entries.is_empty());
    }

    #[test]
    fn parse_reader_handles_invalid_utf8_in_command() {
        let input = b": 1:0;ok\n: 2:0;bad\xff\n: 3:0;again\n".to_vec();
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");
        assert_eq!(entries.len(), 3);
        assert_eq!(entries[1].command, "bad\u{FFFD}");
    }

    #[test]
    fn parse_reader_handles_invalid_utf8_in_fish_command() {
        let input =
            b"- cmd: foo\n  when: 1\n- cmd: bad\xff\n  when: 2\n- cmd: bar\n  when: 3\n".to_vec();
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");
        assert_eq!(entries.len(), 3);
        assert_eq!(entries[1].command, "bad\u{FFFD}");
    }

    #[test]
    fn parse_reader_errors_on_invalid_zsh_metadata() {
        let input = b": 1:\xff;echo bad\n".to_vec();
        let reader = Cursor::new(input);
        let err = parse_entries([(reader, "-")]).expect_err("should error");
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn parse_reader_errors_on_invalid_fish_metadata() {
        let input = b"- cmd: echo\n  when: \xff\n".to_vec();
        let reader = Cursor::new(input);
        let err = parse_entries([(reader, "-")]).expect_err("should error");
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn parse_readers_sorts_by_timestamp() {
        let r1 = Cursor::new(": 2:0;two\n");
        let r2 = Cursor::new(": 1:0;one\n");
        let entries = parse_entries([(r1, "-"), (r2, "-")]).expect("should parse");
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].timestamp, 1);
        assert_eq!(entries[1].timestamp, 2);
    }

    #[test]
    fn parse_readers_preserves_order_with_same_timestamp() {
        let r1 = Cursor::new(": 100:0;b\n");
        let r2 = Cursor::new(": 100:0;a\n");
        let entries = parse_entries([(r1, "-"), (r2, "-")]).expect("should parse");
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].command, "b");
        assert_eq!(entries[1].command, "a");
    }

    #[test]
    fn parse_readers_deduplicates_exact_matches() {
        let r1 = Cursor::new(": 1:0;one\n");
        let r2 = Cursor::new(": 1:0;one\n");
        let entries = parse_entries([(r1, "-"), (r2, "-")]).expect("should parse");
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].timestamp, 1);
        assert_eq!(entries[0].command, "one");
    }

    #[test]
    fn parse_readers_keeps_zero_timestamp_duplicates() {
        let r1 = Cursor::new("echo hi\n");
        let r2 = Cursor::new("echo hi\n");
        let entries = parse_entries([(r1, "-"), (r2, "-")]).expect("should parse");
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].timestamp, 0);
        assert_eq!(entries[1].timestamp, 0);
        assert_eq!(entries[0].command, "echo hi");
        assert_eq!(entries[1].command, "echo hi");
    }

    #[test]
    fn parse_readers_merges_entries_with_richer_info() {
        let zsh = Cursor::new(": 1000:5;echo hello\n");
        let fish = Cursor::new("- cmd: echo hello\n  when: 1000\n  paths:\n    - /tmp\n");
        let entries = parse_entries([(zsh, "-"), (fish, "-")]).expect("should parse");
        assert_eq!(entries.len(), 1);
        let entry = &entries[0];
        assert_eq!(entry.timestamp, 1000);
        assert_eq!(entry.command, "echo hello");
        assert_eq!(entry.duration, 5);
        assert_eq!(entry.paths, vec!["/tmp".to_string()]);
    }

    #[test]
    fn merge_different_format_histories() {
        let sh = Cursor::new("echo sh\n");
        let zsh = Cursor::new(": 1:0;echo zsh\n");
        let fish = Cursor::new("- cmd: echo fish\n  when: 2\n");

        let entries =
            parse_entries([(sh, "sh"), (zsh, "zsh"), (fish, "fish")]).expect("should parse");

        assert_eq!(entries.len(), 3);
        assert_eq!(entries[0].command, "echo sh");
        assert_eq!(entries[1].command, "echo zsh");
        assert_eq!(entries[2].command, "echo fish");
        assert_eq!(entries[0].timestamp, 0);
        assert_eq!(entries[1].timestamp, 1);
        assert_eq!(entries[2].timestamp, 2);
    }

    #[test]
    fn parse_fish_entry_handles_escapes() {
        let input = "- cmd: first\\nsecond\\\\third\\x\n  when: 1700000000\n";
        let reader = Cursor::new(input);
        let entries = parse_entries([(reader, "-")]).expect("should parse");
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
