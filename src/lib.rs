use std::collections::{BTreeMap, HashSet};
use std::io::{BufRead, Cursor, Error, ErrorKind, Result as IoResult, Write};
use std::iter::Peekable;
use std::path::{Path, PathBuf};
use std::str;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HistoryEntry {
    pub timestamp: u64,
    pub duration: u64,
    pub command: String,
    pub paths: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ShellFormat {
    Sh,
    ZshExtended,
    Fish,
}

#[derive(Debug)]
pub struct HistoryEntries {
    pub entries: Vec<HistoryEntry>,
    pub original_formats: HashSet<ShellFormat>,
}

impl HistoryEntries {
    /// Returns the primary format if there's exactly one format, otherwise None.
    ///
    /// This is useful for determining if all input files used the same shell format.
    #[must_use]
    pub fn primary_format(&self) -> Option<ShellFormat> {
        if self.original_formats.len() == 1 {
            self.original_formats.iter().copied().next()
        } else {
            None
        }
    }
}

/// A history file containing a reader and optional path information.
///
/// The reader must implement both `BufRead` for line-by-line reading and
/// `Seek` for repositioning within the file.
#[derive(Debug)]
pub struct HistoryFile<R>
where
    R: BufRead,
{
    /// The reader for accessing the history file contents.
    pub reader: R,
    /// Optional path to the history file (used for error reporting and debugging).
    pub path: Option<PathBuf>,
}

impl<'a> From<&'a str> for HistoryFile<Cursor<&'a str>> {
    /// Creates a new `HistoryFile` instance from a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// let history: histutils::HistoryFile<_> = ": 1234567890:0;echo hello\n".into();
    /// ```
    fn from(content: &'a str) -> Self {
        Self {
            reader: Cursor::new(content),
            path: None,
        }
    }
}

impl<'a, const N: usize> From<&'a [u8; N]> for HistoryFile<Cursor<&'a [u8]>> {
    /// Creates a new `HistoryFile` instance from a byte array.
    ///
    /// # Examples
    ///
    /// ```
    /// let history: histutils::HistoryFile<_> = b": 1234567890:0;echo hello\n".into();
    /// ```
    fn from(content: &'a [u8; N]) -> Self {
        Self {
            reader: Cursor::new(content.as_slice()),
            path: None,
        }
    }
}

/// Parses history entries from multiple files.
///
/// This function combines format detection and entry parsing into a single
/// operation. It first detects the shell format used by the history files,
/// then parses all entries and merges them into a timestamp-sorted collection.
///
/// # Arguments
///
/// * `files` - An iterator of `HistoryFile` instances to parse and analyze.
///
/// # Examples
///
/// ```
/// let zsh_history: histutils::HistoryFile<_> = ": 1609459200:5;echo hello\n: 1609459300:2;ls -la\n".into();
/// let bash_history: histutils::HistoryFile<_> = "echo world\nls\n".into();
///
/// let history = histutils::parse_entries([zsh_history, bash_history]).unwrap();
/// assert!(history.entries.len() >= 2);
/// assert!(history.original_formats.len() == 2); // Mixed formats
/// ```
///
/// # Returns
///
/// Returns parsed `HistoryEntries` struct.
///
/// # Errors
///
/// Returns an error if reading from any file fails or if invalid metadata
/// is encountered in extended shell formats.
pub fn parse_entries<R, I>(files: I) -> IoResult<HistoryEntries>
where
    R: BufRead,
    I: IntoIterator<Item = HistoryFile<R>>,
{
    let mut map: BTreeMap<u64, Vec<HistoryEntry>> = BTreeMap::new();
    let mut original_formats = HashSet::new();

    for history_file in files {
        let path = history_file.path.as_deref().unwrap_or(Path::new("-"));
        let mut reader = history_file.reader;
        let mut buf = Vec::new();
        let mut lines = std::iter::from_fn(move || {
            buf.clear();
            match reader.read_until(b'\n', &mut buf) {
                Ok(0) => None,
                Ok(_) => {
                    if buf.ends_with(b"\n") {
                        buf.pop();
                        if buf.ends_with(b"\r") {
                            buf.pop();
                        }
                    }
                    Some(Ok(buf.clone()))
                }
                Err(e) => Some(Err(e)),
            }
        })
        .peekable();

        let file_format = detect_format_from_lines(&mut lines);
        original_formats.insert(file_format);

        let entries_result = match file_format {
            ShellFormat::Fish => parse_fish_format(&mut lines, Some(path)),
            ShellFormat::ZshExtended => parse_zsh_extended_format(&mut lines, Some(path)),
            ShellFormat::Sh => parse_sh_format(&mut lines, Some(path)),
        };

        for entry in entries_result? {
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

    let entries = map.into_iter().flat_map(|(_, v)| v).collect();

    Ok(HistoryEntries {
        entries,
        original_formats,
    })
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

fn detect_format_from_lines<I>(lines: &mut Peekable<I>) -> ShellFormat
where
    I: Iterator<Item = IoResult<Vec<u8>>>,
{
    if let Some(Ok(first_line)) = lines.peek() {
        detect_format_line(first_line)
    } else {
        ShellFormat::Sh
    }
}

fn parse_sh_format<I>(lines: &mut Peekable<I>, path: Option<&Path>) -> IoResult<Vec<HistoryEntry>>
where
    I: Iterator<Item = IoResult<Vec<u8>>>,
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
    lines: &mut Peekable<I>,
    path: Option<&Path>,
) -> IoResult<Vec<HistoryEntry>>
where
    I: Iterator<Item = IoResult<Vec<u8>>>,
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

fn parse_fish_format<I>(lines: &mut Peekable<I>, path: Option<&Path>) -> IoResult<Vec<HistoryEntry>>
where
    I: Iterator<Item = IoResult<Vec<u8>>>,
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

fn invalid_utf8_error(path: Option<&Path>, line_no: usize) -> Error {
    if let Some(p) = path {
        Error::new(
            ErrorKind::InvalidData,
            format!("invalid UTF-8 in metadata in {}:{line_no}", p.display()),
        )
    } else {
        Error::new(
            ErrorKind::InvalidData,
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
    match str::from_utf8(bytes) {
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

    let ts_str = str::from_utf8(ts_bytes).map_err(|_| LineParseError::InvalidUtf8)?;
    let dur_str = str::from_utf8(dur_bytes).map_err(|_| LineParseError::InvalidUtf8)?;
    let timestamp: u64 = match ts_str.parse() {
        Ok(t) => t,
        Err(_) => return Ok(None),
    };
    let duration: u64 = match dur_str.parse() {
        Ok(d) => d,
        Err(_) => return Ok(None),
    };

    let (command_raw, invalid) = decode_lossy(cmd_bytes);
    let command = unescape_command(&command_raw);

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
    let (command_raw, invalid) = decode_lossy(s);
    let command = unescape_command(&command_raw);
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
    lines: &mut Peekable<I>,
    line_no: &mut usize,
    path: Option<&Path>,
    start_line: usize,
) -> Result<Option<HistoryEntry>, LineParseError>
where
    I: Iterator<Item = IoResult<Vec<u8>>>,
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
            let ts_str = str::from_utf8(ts_bytes).map_err(|_| LineParseError::InvalidUtf8)?;
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
) -> IoResult<()> {
    match format {
        ShellFormat::Sh => write_sh_format(writer, entries),
        ShellFormat::ZshExtended => write_zsh_format(writer, entries),
        ShellFormat::Fish => write_fish_format(writer, entries),
    }
}

fn write_sh_format<W: Write, I: IntoIterator<Item = HistoryEntry>>(
    writer: &mut W,
    entries: I,
) -> IoResult<()> {
    for entry in entries {
        writeln!(writer, "{}", escape_command(&entry.command))?;
    }
    Ok(())
}

fn write_zsh_format<W: Write, I: IntoIterator<Item = HistoryEntry>>(
    writer: &mut W,
    entries: I,
) -> IoResult<()> {
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
) -> IoResult<()> {
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
            '\\' => out.push_str("\\\\"),
            _ => out.push(ch),
        }
    }
    out
}

fn unescape_command(s: &str) -> String {
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

    #[test]
    fn detect_format_none() {
        let readers: Vec<HistoryFile<Cursor<&[u8]>>> = Vec::new();
        let result = parse_entries(readers).unwrap();
        assert_eq!(result.primary_format(), None);
    }

    #[test]
    fn detect_format_one_sh() {
        let history_file: HistoryFile<_> = "echo hello\n".into();
        let result = parse_entries([history_file]).unwrap();
        assert_eq!(result.primary_format(), Some(ShellFormat::Sh));
    }

    #[test]
    fn detect_format_one_zsh() {
        let history_file: HistoryFile<_> = ": 1234567890:0;echo hello\n".into();
        let result = parse_entries([history_file]).unwrap();
        assert_eq!(result.primary_format(), Some(ShellFormat::ZshExtended));
    }

    #[test]
    fn detect_format_one_fish() {
        let history_file: HistoryFile<_> = "- cmd: echo hello\n  when: 1234567890\n".into();
        let result = parse_entries([history_file]).unwrap();
        assert_eq!(result.primary_format(), Some(ShellFormat::Fish));
    }

    #[test]
    fn detect_format_multiple_sh() {
        let h1: HistoryFile<_> = "echo foo\n".into();
        let h2: HistoryFile<_> = "echo bar\n".into();
        let h3: HistoryFile<_> = "echo baz\n".into();
        let result = parse_entries([h1, h2, h3]).unwrap();
        assert_eq!(result.primary_format(), Some(ShellFormat::Sh));
    }

    #[test]
    fn detect_format_multiple_zsh() {
        let h1: HistoryFile<_> = ": 1234567891:0;echo foo\n".into();
        let h2: HistoryFile<_> = ": 1234567892:0;echo bar\n".into();
        let h3: HistoryFile<_> = ": 1234567893:0;echo baz\n".into();
        let result = parse_entries([h1, h2, h3]).unwrap();
        assert_eq!(result.primary_format(), Some(ShellFormat::ZshExtended));
    }

    #[test]
    fn detect_format_multiple_fish() {
        let h1: HistoryFile<_> = "- cmd: echo foo\n  when: 1234567891\n".into();
        let h2: HistoryFile<_> = "- cmd: echo bar\n  when: 1234567892\n".into();
        let h3: HistoryFile<_> = "- cmd: echo baz\n  when: 1234567893\n".into();
        let history = parse_entries([h1, h2, h3]).unwrap();
        assert_eq!(history.primary_format(), Some(ShellFormat::Fish));
    }

    #[test]
    fn detect_format_mixed() {
        let h1: HistoryFile<_> = ": 1234567891:0;echo foo\n".into();
        let h2: HistoryFile<_> = "- cmd: echo bar\n  when: 1234567892\n".into();
        let result = parse_entries([h1, h2]).unwrap();
        assert_eq!(result.primary_format(), None);
    }

    #[test]
    fn parse_simple_entry() {
        let input: HistoryFile<_> = "echo hello\n".into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "echo hello");
    }

    #[test]
    fn parse_simple_entries() {
        let input: HistoryFile<_> = "echo hello\nls -la\npwd\n".into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 3);
        assert_eq!(entries[0].command, "echo hello");
        assert_eq!(entries[1].command, "ls -la");
        assert_eq!(entries[2].command, "pwd");
    }

    #[test]
    fn parse_simple_multiline_entry() {
        let input: HistoryFile<_> = "echo hello\\\nanother\\\nline\n".into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "echo hello\nanother\nline");
    }

    #[test]
    fn parse_extended_entries() {
        let input: HistoryFile<_> = ": 1700000001:0;echo hello\n: 1700000002:5;ls -la\n".into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 2);

        assert_eq!(entries[0].timestamp, 1_700_000_001);
        assert_eq!(entries[0].duration, 0);
        assert_eq!(entries[0].command, "echo hello");

        assert_eq!(entries[1].timestamp, 1_700_000_002);
        assert_eq!(entries[1].duration, 5);
        assert_eq!(entries[1].command, "ls -la");
    }

    #[test]
    fn parse_fish_entry_basic() {
        let input: HistoryFile<_> = "- cmd: cargo build\n  when: 1700000000\n".into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].timestamp, 1_700_000_000);
        assert_eq!(entries[0].command, "cargo build");
    }

    #[test]
    fn parse_fish_entry_with_paths() {
        let input: HistoryFile<_> =
            "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n"
                .into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].paths, vec!["~/Developer/histutils".to_string()]);
    }

    #[test]
    fn parse_fish_entry_multiple_paths() {
        let input: HistoryFile<_> = "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/project1\n    - ~/project2\n".into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 1);
        assert_eq!(
            entries[0].paths,
            vec!["~/project1".to_string(), "~/project2".to_string()]
        );
    }

    #[test]
    fn parse_fish_entry_paths_then_new_entry() {
        let input: HistoryFile<_> = "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/project1\n- cmd: echo hi\n  when: 1700000001\n".into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].paths, vec!["~/project1".to_string()]);
        assert_eq!(entries[1].command, "echo hi");
    }

    #[test]
    fn parse_fish_multiline_command() {
        let input: HistoryFile<_> =
            "- cmd: echo \"hello\\nmultiline\\nstring\"\n  when: 1700000000\n".into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "echo \"hello\nmultiline\nstring\"");
    }

    #[test]
    fn parse_fish_colon_in_command() {
        let input: HistoryFile<_> =
            "- cmd: git commit -m \"Test: something\"\n  when: 1516464765\n".into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].timestamp, 1_516_464_765);
        assert_eq!(entries[0].command, "git commit -m \"Test: something\"");
    }

    #[test]
    fn parse_reader_ignores_invalid_and_empty() {
        let input: HistoryFile<_> = ": invalid\n\n".into();
        let entries = parse_entries([input]).unwrap().entries;
        assert!(entries.is_empty());
    }

    #[test]
    fn parse_reader_handles_invalid_utf8_in_command() {
        let input: HistoryFile<_> = b": 1:0;ok\n: 2:0;bad\xff\n: 3:0;again\n".into();
        let entries = parse_entries([input]).unwrap().entries;
        assert_eq!(entries.len(), 3);
        assert_eq!(entries[1].command, "bad\u{FFFD}");
    }

    #[test]
    fn parse_reader_handles_invalid_utf8_in_fish_command() {
        let input: HistoryFile<_> =
            b"- cmd: foo\n  when: 1\n- cmd: bad\xff\n  when: 2\n- cmd: bar\n  when: 3\n".into();
        let entries = parse_entries([input]).unwrap().entries;
        assert_eq!(entries.len(), 3);
        assert_eq!(entries[1].command, "bad\u{FFFD}");
    }

    #[test]
    fn parse_reader_errors_on_invalid_zsh_metadata() {
        let input: HistoryFile<_> = b": 1:\xff;echo bad\n".into();
        let err = parse_entries([input]).expect_err("should error");
        assert_eq!(err.kind(), ErrorKind::InvalidData);
    }

    #[test]
    fn parse_reader_errors_on_invalid_fish_metadata() {
        let input: HistoryFile<_> = b"- cmd: echo\n  when: \xff\n".into();
        let err = parse_entries([input]).expect_err("should error");
        assert_eq!(err.kind(), ErrorKind::InvalidData);
    }

    #[test]
    fn parse_readers_sorts_by_timestamp() {
        let h1: HistoryFile<_> = ": 2:0;two\n".into();
        let h2: HistoryFile<_> = ": 1:0;one\n".into();
        let entries = parse_entries([h1, h2]).unwrap().entries;
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].timestamp, 1);
        assert_eq!(entries[1].timestamp, 2);
    }

    #[test]
    fn parse_readers_preserves_order_with_same_timestamp() {
        let h1: HistoryFile<_> = ": 100:0;b\n".into();
        let h2: HistoryFile<_> = ": 100:0;a\n".into();
        let entries = parse_entries([h1, h2]).unwrap().entries;
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].command, "b");
        assert_eq!(entries[1].command, "a");
    }

    #[test]
    fn parse_readers_deduplicates_exact_matches() {
        let h1: HistoryFile<_> = ": 1:0;one\n".into();
        let h2: HistoryFile<_> = ": 1:0;one\n".into();
        let entries = parse_entries([h1, h2]).unwrap().entries;
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].timestamp, 1);
        assert_eq!(entries[0].command, "one");
    }

    #[test]
    fn parse_readers_keeps_zero_timestamp_duplicates() {
        let h1: HistoryFile<_> = "echo hi\n".into();
        let h2: HistoryFile<_> = "echo hi\n".into();
        let entries = parse_entries([h1, h2]).expect("should parse").entries;
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].timestamp, 0);
        assert_eq!(entries[1].timestamp, 0);
        assert_eq!(entries[0].command, "echo hi");
        assert_eq!(entries[1].command, "echo hi");
    }

    #[test]
    fn parse_readers_merges_entries_with_richer_info() {
        let zsh: HistoryFile<_> = ": 1000:5;echo hello\n".into();
        let fish: HistoryFile<_> = "- cmd: echo hello\n  when: 1000\n  paths:\n    - /tmp\n".into();
        let entries = parse_entries([zsh, fish]).unwrap().entries;
        assert_eq!(entries.len(), 1);
        let entry = &entries[0];
        assert_eq!(entry.timestamp, 1000);
        assert_eq!(entry.command, "echo hello");
        assert_eq!(entry.duration, 5);
        assert_eq!(entry.paths, vec!["/tmp".to_string()]);
    }

    #[test]
    fn merge_different_format_histories() {
        let sh: HistoryFile<_> = "echo sh\n".into();
        let zsh: HistoryFile<_> = ": 1:0;echo zsh\n".into();
        let fish: HistoryFile<_> = "- cmd: echo fish\n  when: 2\n".into();
        let entries = parse_entries([sh, zsh, fish]).unwrap().entries;

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
        let input: HistoryFile<_> =
            "- cmd: first\\nsecond\\\\third\\x\n  when: 1700000000\n".into();
        let entries = parse_entries([input]).unwrap().entries;
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "first\nsecond\\third\\x");
    }

    #[test]
    fn write_sh_single_entry() {
        let entries = vec![HistoryEntry {
            timestamp: 0,
            duration: 0,
            command: "echo hello".to_string(),
            paths: Vec::new(),
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
        assert_eq!(output, b"echo hello\n");
    }

    #[test]
    fn write_zsh_single_entry() {
        let entries = vec![HistoryEntry {
            timestamp: 1,
            duration: 0,
            command: "echo hello".to_string(),
            paths: Vec::new(),
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
        assert_eq!(output, b": 1:0;echo hello\n");
    }

    #[test]
    fn write_fish_single_entry() {
        let entries = vec![HistoryEntry {
            timestamp: 1,
            duration: 0,
            command: "echo hello".to_string(),
            paths: Vec::new(),
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
        assert_eq!(output, b"- cmd: echo hello\n  when: 1\n");
    }

    #[test]
    fn write_sh_multiple_entries() {
        let entries = vec![
            HistoryEntry {
                timestamp: 0,
                duration: 0,
                command: "echo foo".to_string(),
                paths: Vec::new(),
            },
            HistoryEntry {
                timestamp: 0,
                duration: 0,
                command: "echo bar".to_string(),
                paths: Vec::new(),
            },
        ];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
        assert_eq!(output, b"echo foo\necho bar\n");
    }

    #[test]
    fn write_zsh_multiple_entries() {
        let entries = vec![
            HistoryEntry {
                timestamp: 1,
                duration: 0,
                command: "echo foo".to_string(),
                paths: Vec::new(),
            },
            HistoryEntry {
                timestamp: 2,
                duration: 0,
                command: "echo bar".to_string(),
                paths: Vec::new(),
            },
        ];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
        assert_eq!(output, b": 1:0;echo foo\n: 2:0;echo bar\n");
    }

    #[test]
    fn write_fish_multiple_entries() {
        let entries = vec![
            HistoryEntry {
                timestamp: 1,
                duration: 0,
                command: "echo foo".to_string(),
                paths: Vec::new(),
            },
            HistoryEntry {
                timestamp: 2,
                duration: 0,
                command: "echo bar".to_string(),
                paths: Vec::new(),
            },
        ];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
        assert_eq!(
            output,
            b"- cmd: echo foo\n  when: 1\n- cmd: echo bar\n  when: 2\n"
        );
    }

    #[test]
    fn write_fish_path() {
        let entries = vec![HistoryEntry {
            timestamp: 1_700_000_000,
            duration: 100,
            command: "cargo build".to_string(),
            paths: vec!["~/Developer/histutils".to_string()],
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).expect("should write");
        assert_eq!(
            output,
            b"- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n"
        );
    }

    #[test]
    fn write_fish_paths() {
        let entries = vec![HistoryEntry {
            timestamp: 1_700_000_000,
            duration: 100,
            command: "cargo build".to_string(),
            paths: vec!["~/Developer/histutils".to_string(), "/tmp".to_string()],
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).expect("should write");
        assert_eq!(
            output,
            b"- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n    - /tmp\n"
        );
    }

    #[test]
    fn write_sh_escape_backslash() {
        let entries = vec![HistoryEntry {
            timestamp: 0,
            duration: 0,
            command: "echo hello \\ world".to_string(),
            paths: Vec::new(),
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
        assert_eq!(output, b"echo hello \\\\ world\n");
    }

    #[test]
    fn write_zsh_escape_backslash() {
        let entries = vec![HistoryEntry {
            timestamp: 1,
            duration: 0,
            command: "echo hello \\ world".to_string(),
            paths: Vec::new(),
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
        assert_eq!(output, b": 1:0;echo hello \\\\ world\n");
    }

    #[test]
    fn write_fish_escape_backslash() {
        let entries = vec![HistoryEntry {
            timestamp: 1,
            duration: 0,
            command: "echo hello \\ world".to_string(),
            paths: Vec::new(),
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
        assert_eq!(output, b"- cmd: echo hello \\\\ world\n  when: 1\n");
    }

    #[test]
    fn write_sh_escape_newline() {
        let entries = vec![HistoryEntry {
            timestamp: 0,
            duration: 0,
            command: "echo hello\nworld".to_string(),
            paths: Vec::new(),
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
        assert_eq!(output, b"echo hello\\\nworld\n");
    }

    #[test]
    fn write_zsh_escape_newline() {
        let entries = vec![HistoryEntry {
            timestamp: 1,
            duration: 0,
            command: "echo hello\nworld".to_string(),
            paths: Vec::new(),
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
        assert_eq!(output, b": 1:0;echo hello\\\nworld\n");
    }

    #[test]
    fn write_fish_escape_newline() {
        let entries = vec![HistoryEntry {
            timestamp: 1,
            duration: 0,
            command: "echo hello\nworld".to_string(),
            paths: Vec::new(),
        }];

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
        assert_eq!(output, b"- cmd: echo hello\\nworld\n  when: 1\n");
    }

    #[test]
    fn roundtrip_sh_backslash() {
        let original = b"echo foo \\\\ hello\n";
        let input: HistoryFile<_> = original.into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "echo foo \\ hello");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
        assert_eq!(output, original);
    }

    #[test]
    fn roundtrip_sh_multiline() {
        let original = b"echo foo\\\nbar\\\nbaz\n";
        let input: HistoryFile<_> = original.into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].command, "echo foo\nbar\nbaz");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
        assert_eq!(output, original);
    }

    #[test]
    fn roundtrip_zsh_multiline() {
        let original = b": 1700000001:0;echo hello\\\nworld\n: 1700000002:5;ls -la\n";

        let input: HistoryFile<_> = original.into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].command, "echo hello\nworld");
        assert_eq!(entries[1].command, "ls -la");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
        assert_eq!(output, original);
    }

    #[test]
    fn roundtrip_zsh_colon_continuation() {
        let original = b": 100:0;echo foo\\\n: 200:0;echo bar\n";
        let input: HistoryFile<_> = original.into();
        let entries = parse_entries([input]).unwrap().entries;

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].timestamp, 100);
        assert_eq!(entries[0].command, "echo foo\n: 200:0;echo bar");

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
        assert_eq!(output, original);
    }

    #[test]
    fn roundtrip_fish_multiline() {
        let original =
            b"- cmd: echo hello\\nworld\n  when: 1700000001\n- cmd: ls\n  when: 1700000002\n";
        let input: HistoryFile<_> = original.into();
        let entries = parse_entries([input]).unwrap().entries;

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
        assert_eq!(output, original);
    }

    #[test]
    fn roundtrip_fish_with_paths() {
        let original = b"- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n- cmd: ls\n  when: 1700000001\n";
        let input: HistoryFile<_> = original.into();
        let entries = parse_entries([input]).unwrap().entries;

        let mut output = Vec::new();
        write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
        assert_eq!(output, original);
    }
}
