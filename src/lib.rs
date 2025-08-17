use std::collections::{BTreeMap, HashSet};
use std::io::{BufRead, Cursor, Result as IoResult, Write};

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

/// Detects the shell format of `BufRead` type.
///
/// Peeks into buffer and does not advance the reader position.
///
/// # Examples
///
/// ```
/// let mut reader = std::io::Cursor::new(b"echo hello\n");
/// assert_eq!(histutils::detect_format(&mut reader), histutils::ShellFormat::Sh);
///
/// let mut reader = std::io::Cursor::new(b": 1234:0;echo hello\n");
/// assert_eq!(histutils::detect_format(&mut reader), histutils::ShellFormat::ZshExtended);
///
/// let mut reader = std::io::Cursor::new(b"- cmd: echo hello\n  when: 1234\n");
/// assert_eq!(histutils::detect_format(&mut reader), histutils::ShellFormat::Fish);
/// ```
///
/// # Returns
/// The detected shell format.
pub fn detect_format<R>(reader: &mut R) -> ShellFormat
where
    R: BufRead,
{
    let buf = reader.fill_buf().unwrap_or(&[]);
    if buf.starts_with(b"- cmd:") {
        ShellFormat::Fish
    } else if buf.starts_with(b":") {
        ShellFormat::ZshExtended
    } else {
        ShellFormat::Sh
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

        let file_format = detect_format(&mut reader);
        original_formats.insert(file_format);

        let entries_iter: Box<dyn Iterator<Item = IoResult<HistoryEntry>>> = match file_format {
            ShellFormat::Fish => Box::new(parse_fish_entries(&mut reader, path)),
            ShellFormat::ZshExtended => Box::new(parse_zsh_extended_entries(&mut reader, path)),
            ShellFormat::Sh => Box::new(parse_sh_entries(&mut reader, path)),
        };

        for entry_result in entries_iter {
            let entry = entry_result?;
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

enum ParseError {
    BadZshExtendedHeader,
    BadFishHeader,
    ParseIntError,
    Utf8Error,
}

impl From<std::num::ParseIntError> for ParseError {
    fn from(_: std::num::ParseIntError) -> Self {
        ParseError::ParseIntError
    }
}

impl From<std::str::Utf8Error> for ParseError {
    fn from(_: std::str::Utf8Error) -> Self {
        ParseError::Utf8Error
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::BadZshExtendedHeader => write!(f, "bad zsh extended header"),
            ParseError::BadFishHeader => write!(f, "bad fish header"),
            ParseError::ParseIntError => write!(f, "parse int error"),
            ParseError::Utf8Error => write!(f, "utf8 error"),
        }
    }
}

struct RawLines<'a, R>
where
    R: BufRead,
{
    reader: &'a mut R,
    buf: Vec<u8>,
    line_no: usize,
}

impl<'a, R> RawLines<'a, R>
where
    R: BufRead,
{
    fn new(reader: &'a mut R) -> Self {
        Self {
            reader,
            buf: Vec::new(),
            line_no: 0,
        }
    }
}

impl<R> Iterator for RawLines<'_, R>
where
    R: BufRead,
{
    type Item = IoResult<(Vec<u8>, usize)>;

    fn next(&mut self) -> Option<Self::Item> {
        self.buf.clear();
        self.line_no += 1;
        match self.reader.read_until(b'\n', &mut self.buf) {
            Ok(0) => None,
            Ok(_) => Some(Ok((self.buf.clone(), self.line_no))),
            Err(e) => Some(Err(e)),
        }
    }
}

struct ShellHistLines<'a, R>
where
    R: BufRead,
{
    raw_lines: RawLines<'a, R>,
}

impl<'a, R> ShellHistLines<'a, R>
where
    R: BufRead,
{
    fn new(reader: &'a mut R) -> Self {
        Self {
            raw_lines: RawLines::new(reader),
        }
    }
}

impl<R> Iterator for ShellHistLines<'_, R>
where
    R: BufRead,
{
    type Item = IoResult<(Vec<u8>, usize)>;

    fn next(&mut self) -> Option<Self::Item> {
        // Get the first line
        let (mut line, start_line) = match self.raw_lines.next() {
            Some(Ok((line, line_no))) => (line, line_no),
            Some(Err(e)) => return Some(Err(e)),
            None => return None,
        };

        // Remove trailing newline if present
        if line.ends_with(b"\n") {
            line.pop();
        }

        // Handle backslash continuation
        while line.ends_with(b"\\") {
            line.pop(); // Remove the backslash
            line.push(b'\n'); // Replace with newline

            // Read the next line
            match self.raw_lines.next() {
                Some(Ok((mut next_line, _))) => {
                    if next_line.ends_with(b"\n") {
                        next_line.pop();
                    }
                    line.extend_from_slice(&next_line);
                }
                Some(Err(e)) => return Some(Err(e)),
                None => break, // EOF
            }
        }

        Some(Ok((line, start_line)))
    }
}

fn parse_sh_entries<'a, R>(
    reader: &'a mut R,
    path: &Path,
) -> impl Iterator<Item = IoResult<HistoryEntry>> + 'a
where
    R: BufRead,
{
    let path = path.to_owned();
    ShellHistLines::new(reader).map(move |entry_res| {
        let (line, lineno) = entry_res?;
        let command = if let Ok(s) = str::from_utf8(&line) {
            s.to_string()
        } else {
            eprintln!("{}:{lineno}: invalid UTF-8", path.display());
            String::from_utf8_lossy(&line).to_string()
        };
        Ok(HistoryEntry {
            timestamp: 0,
            duration: 0,
            command,
            paths: vec![],
        })
    })
}

fn parse_zsh_extended_entries<'a, R>(
    reader: &'a mut R,
    path: &Path,
) -> impl Iterator<Item = IoResult<HistoryEntry>> + 'a
where
    R: BufRead,
{
    let path = path.to_owned();
    ShellHistLines::new(reader).filter_map(move |entry_res| match entry_res {
        Ok((line, lineno)) => match parse_zsh_raw_entry(&line) {
            Ok(entry) => Some(Ok(entry)),
            Err(err) => {
                eprintln!("{}:{lineno}: {err}", path.display());
                None
            }
        },
        Err(err) => Some(Err(err)),
    })
}

fn parse_zsh_raw_entry(line: &[u8]) -> Result<HistoryEntry, ParseError> {
    if !line.starts_with(b":") {
        return Err(ParseError::BadZshExtendedHeader);
    }

    let Some(idx_colon) = line[1..].iter().position(|&b| b == b':') else {
        return Err(ParseError::BadZshExtendedHeader);
    };

    let ts_bytes = &line[2..=idx_colon];

    let Some(idx_sc) = line[idx_colon + 2..].iter().position(|&b| b == b';') else {
        return Err(ParseError::BadZshExtendedHeader);
    };

    let dur_bytes = &line[idx_colon + 2..idx_colon + 2 + idx_sc];
    let cmd_bytes = &line[idx_colon + 3 + idx_sc..];

    let ts_str = str::from_utf8(ts_bytes)?;
    let dur_str = str::from_utf8(dur_bytes)?;
    let timestamp = ts_str.parse()?;
    let duration = dur_str.parse()?;

    if let Ok(s) = str::from_utf8(cmd_bytes) {
        let command = s.to_string();
        Ok(HistoryEntry {
            timestamp,
            duration,
            command,
            paths: Vec::new(),
        })
    } else {
        let command = String::from_utf8_lossy(cmd_bytes).to_string();
        Ok(HistoryEntry {
            timestamp,
            duration,
            command,
            paths: Vec::new(),
        })
    }
}

struct FishHistEntries<'a, R>
where
    R: BufRead,
{
    raw_lines: RawLines<'a, R>,
    current_entry: Vec<u8>,
    in_entry: bool,
    entry_start_line: usize,
}

impl<'a, R> FishHistEntries<'a, R>
where
    R: BufRead,
{
    fn new(reader: &'a mut R) -> Self {
        Self {
            raw_lines: RawLines::new(reader),
            current_entry: Vec::new(),
            in_entry: false,
            entry_start_line: 0,
        }
    }
}

impl<R> Iterator for FishHistEntries<'_, R>
where
    R: BufRead,
{
    type Item = IoResult<(Vec<u8>, usize)>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.raw_lines.next() {
                Some(Ok((line, line_no))) => {
                    if line.starts_with(b"- cmd:") {
                        // Start of new entry
                        if self.in_entry && !self.current_entry.is_empty() {
                            // Return previous entry
                            let entry = self.current_entry.clone();
                            let entry_line = self.entry_start_line;
                            self.current_entry.clear();
                            self.current_entry.extend_from_slice(&line);
                            self.entry_start_line = line_no;
                            return Some(Ok((entry, entry_line)));
                        }
                        // First entry
                        self.in_entry = true;
                        self.current_entry.clear();
                        self.current_entry.extend_from_slice(&line);
                        self.entry_start_line = line_no;
                    } else if self.in_entry {
                        // Continue current entry
                        self.current_entry.extend_from_slice(&line);
                    }
                }
                Some(Err(e)) => return Some(Err(e)),
                None => {
                    // EOF
                    if self.in_entry && !self.current_entry.is_empty() {
                        let entry = self.current_entry.clone();
                        let entry_line = self.entry_start_line;
                        self.current_entry.clear();
                        self.in_entry = false;
                        return Some(Ok((entry, entry_line)));
                    }
                    return None;
                }
            }
        }
    }
}

fn parse_fish_entries<'a, R>(
    reader: &'a mut R,
    path: &Path,
) -> impl Iterator<Item = IoResult<HistoryEntry>> + 'a
where
    R: BufRead,
{
    let path = path.to_owned();
    FishHistEntries::new(reader).filter_map(move |entry_res| match entry_res {
        Ok((entry_data, lineno)) => match parse_fish_raw_entry(&entry_data) {
            Ok(entry) => Some(Ok(entry)),
            Err(err) => {
                eprintln!("{}:{lineno}: {err}", path.display());
                None
            }
        },
        Err(err) => Some(Err(err)),
    })
}

fn parse_fish_raw_entry(data: &[u8]) -> Result<HistoryEntry, ParseError> {
    let lines: Vec<&[u8]> = data.split(|&b| b == b'\n').collect();

    if lines.is_empty() {
        return Err(ParseError::BadFishHeader);
    }

    let Some(cmd_bytes) = lines[0].strip_prefix(b"- cmd:") else {
        return Err(ParseError::BadFishHeader);
    };
    let cmd_bytes = cmd_bytes.strip_prefix(b" ").unwrap_or(cmd_bytes);
    let command = unescape_fish(&String::from_utf8_lossy(cmd_bytes));

    if lines.len() < 2 {
        return Err(ParseError::BadFishHeader);
    }

    let timestamp: u64;
    let line = lines[1].strip_prefix(b"  ").unwrap_or(lines[1]);
    if let Some(rest) = line.strip_prefix(b"when:") {
        let ts_bytes = rest.strip_prefix(b" ").unwrap_or(rest);
        let ts = str::from_utf8(ts_bytes)?.parse()?;
        timestamp = ts;
    } else {
        return Err(ParseError::BadFishHeader);
    }

    let mut paths: Vec<String> = Vec::new();
    if lines.len() > 2 {
        let line = lines[2].strip_prefix(b"  ").unwrap_or(lines[2]);
        if line.strip_prefix(b"paths:").is_some() {
            let mut i = 3;
            while i < lines.len() {
                let Some(path_line) = lines[i].strip_prefix(b"    ") else {
                    break;
                };
                if path_line.is_empty() {
                    break;
                }
                if let Some(path_bytes) = path_line.strip_prefix(b"- ") {
                    let path_str = str::from_utf8(path_bytes)?;
                    paths.push(path_str.to_string());
                } else {
                    break;
                }
                i += 1;
            }
        }
    }

    Ok(HistoryEntry {
        timestamp,
        duration: 0,
        command,
        paths,
    })
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

/// Writes history entries in the specified format.
///
/// # Arguments
///
/// * `writer` - A mutable reference to any type implementing `Write` (e.g., `File`, `Vec<u8>`, `stdout`)
/// * `entries` - An iterator over `HistoryEntry` items to be written
/// * `format` - The shell format to use for output (`Sh`, `ZshExtended`, or `Fish`)
///
/// # Returns
///
/// Returns `Ok(())` on success, or an `io::Result` error if writing fails.
///
/// # Errors
///
/// Returns an error if writing to the output fails.
///
/// # Example
///
/// ```
/// let entries = vec![
///     histutils::HistoryEntry {
///         timestamp: 1640995200,
///         duration: 1000,
///         command: "ls -la".to_string(),
///         paths: vec!["/home/user".to_string()],
///     },
///     histutils::HistoryEntry {
///         timestamp: 1640995260,
///         duration: 500,
///         command: "git status".to_string(),
///         paths: vec!["/home/user/project".to_string()],
///     },
/// ];
///
/// let mut output = std::io::Cursor::new(Vec::new());
/// histutils::write_entries(&mut output, entries, histutils::ShellFormat::Sh)?;
/// # Ok::<(), std::io::Error>(())
/// ```
pub fn write_entries<W, I>(writer: &mut W, entries: I, format: ShellFormat) -> IoResult<()>
where
    W: Write,
    I: IntoIterator<Item = HistoryEntry>,
{
    match format {
        ShellFormat::Sh => write_sh_entries(writer, entries),
        ShellFormat::ZshExtended => write_zsh_entries(writer, entries),
        ShellFormat::Fish => write_fish_entries(writer, entries),
    }
}

/// Writes history entries in sh/bash shell format.
///
/// This function outputs history entries as plain command lines, one per line,
/// with proper escaping for newlines and backslashes.
///
/// # Arguments
///
/// * `writer` - A mutable reference to any type implementing `Write` (e.g., `File`, `Vec<u8>`, `stdout`)
/// * `entries` - An iterator over `HistoryEntry` items to be written in sh format
///
/// # Returns
///
/// Returns `Ok(())` on success, or an `io::Result` error if writing fails.
///
/// # Errors
///
/// Returns an error if writing to the output fails.
pub fn write_sh_entries<W, I>(writer: &mut W, entries: I) -> IoResult<()>
where
    W: Write,
    I: IntoIterator<Item = HistoryEntry>,
{
    for entry in entries {
        writeln!(writer, "{}", entry.command.replace('\n', "\\\n"))?;
    }
    Ok(())
}

/// Writes history entries in zsh extended format.
///
/// This function outputs history entries in zsh's extended history format,
/// including timestamps, duration, and commands with proper escaping.
///
/// # Arguments
///
/// * `writer` - A mutable reference to any type implementing `Write` (e.g., `File`, `Vec<u8>`, `stdout`)
/// * `entries` - An iterator over `HistoryEntry` items to be written in zsh extended format
///
/// # Returns
///
/// Returns `Ok(())` on success, or an `io::Result` error if writing fails.
///
/// # Errors
///
/// Returns an error if writing to the output fails.
pub fn write_zsh_entries<W, I>(writer: &mut W, entries: I) -> IoResult<()>
where
    W: Write,
    I: IntoIterator<Item = HistoryEntry>,
{
    for entry in entries {
        writeln!(
            writer,
            ": {}:{};{}",
            entry.timestamp,
            entry.duration,
            entry.command.replace('\n', "\\\n")
        )?;
    }
    Ok(())
}

/// Writes history entries in Fish shell format.
///
/// This function outputs history entries in Fish shell's YAML-based history format,
/// including command text, timestamps, and associated file paths.
///
/// # Arguments
///
/// * `writer` - A mutable reference to any type implementing `Write` (e.g., `File`, `Vec<u8>`, `stdout`)
/// * `entries` - An iterator over `HistoryEntry` items to be written in Fish format
///
/// # Returns
///
/// Returns `Ok(())` on success, or an `io::Result` error if writing fails.
///
/// # Errors
///
/// Returns an error if writing to the output fails.
pub fn write_fish_entries<W, I>(writer: &mut W, entries: I) -> IoResult<()>
where
    W: Write,
    I: IntoIterator<Item = HistoryEntry>,
{
    for entry in entries {
        writeln!(
            writer,
            "- cmd: {}",
            entry.command.replace('\\', "\\\\").replace('\n', "\\n")
        )?;
        writeln!(writer, "  when: {}", entry.timestamp)?;
        if !entry.paths.is_empty() {
            writeln!(writer, "  paths:")?;
            for p in entry.paths {
                writeln!(writer, "    - {}", &p)?;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    mod detect_format {
        use super::{ShellFormat, detect_format};
        use std::io::Cursor;

        #[test]
        fn empty_fallback() {
            let mut reader = Cursor::new(b"");
            assert_eq!(detect_format(&mut reader), ShellFormat::Sh);
            assert_eq!(reader.position(), 0);
        }

        #[test]
        fn sh() {
            let mut reader = Cursor::new(b"echo hello\n");
            assert_eq!(detect_format(&mut reader), ShellFormat::Sh);
            assert_eq!(reader.position(), 0);
        }

        #[test]
        fn zsh_extended() {
            let mut reader = Cursor::new(b": 1234:0;echo hello\n");
            assert_eq!(detect_format(&mut reader), ShellFormat::ZshExtended);
            assert_eq!(reader.position(), 0);
        }

        #[test]
        fn fish() {
            let mut reader = Cursor::new(b"- cmd: echo hello\n  when: 1234\n");
            assert_eq!(detect_format(&mut reader), ShellFormat::Fish);
            assert_eq!(reader.position(), 0);
        }
    }

    mod parse_entries_primary_format {
        use super::{HistoryFile, ShellFormat, parse_entries};
        use std::io::Cursor;

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
    }

    mod parse_sh_entries {
        use super::parse_sh_entries;
        use std::{io::Cursor, path::PathBuf};

        #[test]
        fn empty() {
            let mut input = Cursor::new("");
            let path = PathBuf::from(".history");
            let mut entries = parse_sh_entries(&mut input, &path);
            assert!(entries.next().is_none());
        }

        #[test]
        fn multiple() {
            let mut input = Cursor::new("foo\nbar\nbaz\n");
            let path = PathBuf::from(".history");
            let mut entries = parse_sh_entries(&mut input, &path);
            assert_eq!("foo", entries.next().unwrap().unwrap().command);
            assert_eq!("bar", entries.next().unwrap().unwrap().command);
            assert_eq!("baz", entries.next().unwrap().unwrap().command);
            assert!(entries.next().is_none());
        }
    }

    mod parse_zsh_extended_entries {
        use super::parse_zsh_extended_entries;
        use std::{io::Cursor, path::PathBuf};

        #[test]
        fn empty() {
            let mut input = Cursor::new("");
            let path = PathBuf::from(".zsh_history");
            let mut entries = parse_zsh_extended_entries(&mut input, &path);
            assert!(entries.next().is_none());
        }

        #[test]
        fn multiple() {
            let mut input = Cursor::new(": 1:0;foo\n: 2:0;bar\n: 3:0;baz\n");
            let path = PathBuf::from(".zsh_history");
            let mut entries = parse_zsh_extended_entries(&mut input, &path);
            assert_eq!("foo", entries.next().unwrap().unwrap().command);
            assert_eq!("bar", entries.next().unwrap().unwrap().command);
            assert_eq!("baz", entries.next().unwrap().unwrap().command);
            assert!(entries.next().is_none());
        }
    }

    mod parse_entries {
        use super::{HistoryFile, parse_entries};

        mod sh {
            use super::{HistoryFile, parse_entries};

            #[test]
            fn single() {
                let input: HistoryFile<_> = "echo hello\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].command, "echo hello");
            }

            #[test]
            fn multiple() {
                let input: HistoryFile<_> = "echo hello\nls -la\npwd\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 3);
                assert_eq!(entries[0].command, "echo hello");
                assert_eq!(entries[1].command, "ls -la");
                assert_eq!(entries[2].command, "pwd");
            }

            #[test]
            fn multiline() {
                let input: HistoryFile<_> = "echo hello\\\nanother\\\nline\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].command, "echo hello\nanother\nline");
            }

            #[test]
            fn backslash() {
                let input: HistoryFile<_> = "echo hello \\ world\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].command, "echo hello \\ world");
            }

            #[test]
            fn double_backslash() {
                let input: HistoryFile<_> = "echo hello \\\\ world\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].command, "echo hello \\\\ world");
            }

            #[test]
            fn lossy_decode_invalid_utf8_command() {
                let input: HistoryFile<_> = b"foo\nbar\xff\nbaz\n".into();
                let entries = parse_entries([input]).unwrap().entries;
                assert_eq!(entries.len(), 3);
                assert_eq!(entries[0].command, "foo");
                assert_eq!(entries[1].command, "bar\u{FFFD}");
                assert_eq!(entries[2].command, "baz");
            }

            #[test]
            fn keeps_duplicates() {
                let h1: HistoryFile<_> = "echo hi\n".into();
                let h2: HistoryFile<_> = "echo hi\n".into();
                let entries = parse_entries([h1, h2]).expect("should parse").entries;
                assert_eq!(entries.len(), 2);
                assert_eq!(entries[0].timestamp, 0);
                assert_eq!(entries[1].timestamp, 0);
                assert_eq!(entries[0].command, "echo hi");
                assert_eq!(entries[1].command, "echo hi");
            }
        }

        mod zsh {
            use super::{HistoryFile, parse_entries};

            #[test]
            fn multiline() {
                let input: HistoryFile<_> =
                    ": 1700000001:0;echo hello\n: 1700000002:5;ls -la\n".into();
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
            fn skips_invalid_extended_header() {
                let input: HistoryFile<_> = ": invalid\n\n".into();
                let entries = parse_entries([input]).unwrap().entries;
                assert!(entries.is_empty());
            }

            #[test]
            fn lossy_decode_invalid_utf8_command() {
                let input: HistoryFile<_> = b": 1:0;foo\n: 2:0;bar\xff\n: 3:0;baz\n".into();
                let entries = parse_entries([input]).unwrap().entries;
                assert_eq!(entries.len(), 3);
                assert_eq!(entries[0].command, "foo");
                assert_eq!(entries[1].command, "bar\u{FFFD}");
                assert_eq!(entries[2].command, "baz");
            }

            #[test]
            fn skips_invalid_zsh_header() {
                let input: HistoryFile<_> = b": 1:0;foo\n: 2:\xff;bar\n: 3:0;baz\n".into();
                let entries = parse_entries([input]).unwrap().entries;
                assert_eq!(entries.len(), 2);
                assert_eq!(entries[0].command, "foo");
                assert_eq!(entries[1].command, "baz");
            }

            #[test]
            fn sorts_by_timestamp() {
                let h1: HistoryFile<_> = ": 2:0;two\n".into();
                let h2: HistoryFile<_> = ": 1:0;one\n".into();
                let entries = parse_entries([h1, h2]).unwrap().entries;
                assert_eq!(entries.len(), 2);
                assert_eq!(entries[0].timestamp, 1);
                assert_eq!(entries[1].timestamp, 2);
            }

            #[test]
            fn preserves_order_with_same_timestamp() {
                let h1: HistoryFile<_> = ": 100:0;b\n".into();
                let h2: HistoryFile<_> = ": 100:0;a\n".into();
                let entries = parse_entries([h1, h2]).unwrap().entries;
                assert_eq!(entries.len(), 2);
                assert_eq!(entries[0].command, "b");
                assert_eq!(entries[1].command, "a");
            }

            #[test]
            fn deduplicates_exact_matches() {
                let h1: HistoryFile<_> = ": 1:0;one\n".into();
                let h2: HistoryFile<_> = ": 1:0;one\n".into();
                let entries = parse_entries([h1, h2]).unwrap().entries;
                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].timestamp, 1);
                assert_eq!(entries[0].command, "one");
            }
        }

        mod fish {
            use super::{HistoryFile, parse_entries};

            #[test]
            fn single() {
                let input: HistoryFile<_> = "- cmd: cargo build\n  when: 1700000000\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].timestamp, 1_700_000_000);
                assert_eq!(entries[0].command, "cargo build");
            }

            #[test]
            fn paths_single() {
                let input: HistoryFile<_> =
                    "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n"
                        .into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].paths, vec!["~/Developer/histutils".to_string()]);
            }

            #[test]
            fn paths_multiple() {
                let input: HistoryFile<_> = "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/project1\n    - ~/project2\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 1);
                assert_eq!(
                    entries[0].paths,
                    vec!["~/project1".to_string(), "~/project2".to_string()]
                );
            }

            #[test]
            fn paths_then_new_entry() {
                let input: HistoryFile<_> = "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/project1\n- cmd: echo hi\n  when: 1700000001\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 2);
                assert_eq!(entries[0].paths, vec!["~/project1".to_string()]);
                assert_eq!(entries[1].command, "echo hi");
            }

            #[test]
            fn multiline_command() {
                let input: HistoryFile<_> =
                    "- cmd: echo \"hello\\nmultiline\\nstring\"\n  when: 1700000000\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].command, "echo \"hello\nmultiline\nstring\"");
            }

            #[test]
            fn colon_in_command() {
                let input: HistoryFile<_> =
                    "- cmd: git commit -m \"Test: something\"\n  when: 1516464765\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].timestamp, 1_516_464_765);
                assert_eq!(entries[0].command, "git commit -m \"Test: something\"");
            }

            #[test]
            fn handles_escapes() {
                let input: HistoryFile<_> =
                    "- cmd: first\\nsecond\\\\third\\x\n  when: 1700000000\n".into();
                let entries = parse_entries([input]).unwrap().entries;
                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].command, "first\nsecond\\third\\x");
            }

            #[test]
            fn handles_invalid_utf8_in_cmd() {
                let input: HistoryFile<_> =
                    b"- cmd: foo\n  when: 1\n- cmd: bad\xff\n  when: 2\n- cmd: bar\n  when: 3\n"
                        .into();
                let entries = parse_entries([input]).unwrap().entries;
                assert_eq!(entries.len(), 3);
                assert_eq!(entries[1].command, "bad\u{FFFD}");
            }

            #[test]
            fn errors_on_invalid_metadata() {
                let input: HistoryFile<_> = b"- cmd: echo\n  when: \xff\n".into();
                let entries = parse_entries([input]).unwrap().entries;
                assert_eq!(entries.len(), 0);
            }

            #[test]
            fn merges_entries_with_richer_info() {
                let zsh: HistoryFile<_> = ": 1000:5;echo hello\n".into();
                let fish: HistoryFile<_> =
                    "- cmd: echo hello\n  when: 1000\n  paths:\n    - /tmp\n".into();
                let entries = parse_entries([zsh, fish]).unwrap().entries;
                assert_eq!(entries.len(), 1);
                let entry = &entries[0];
                assert_eq!(entry.timestamp, 1000);
                assert_eq!(entry.command, "echo hello");
                assert_eq!(entry.duration, 5);
                assert_eq!(entry.paths, vec!["/tmp".to_string()]);
            }
        }

        #[test]
        fn merge_multiple_formats() {
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
    }

    mod write_entries {
        use super::{HistoryEntry, ShellFormat, write_entries};

        mod sh {
            use super::{HistoryEntry, ShellFormat, write_entries};

            #[test]
            fn single() {
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
            fn multiple() {
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
            fn no_escape_backslash() {
                let entries = vec![HistoryEntry {
                    timestamp: 0,
                    duration: 0,
                    command: "echo hello \\ world".to_string(),
                    paths: Vec::new(),
                }];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
                assert_eq!(output, b"echo hello \\ world\n");
            }

            #[test]
            fn escape_newline() {
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
        }

        mod zsh {
            use super::{HistoryEntry, ShellFormat, write_entries};

            #[test]
            fn single() {
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
            fn multiple() {
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
            fn no_escape_backslash() {
                let entries = vec![HistoryEntry {
                    timestamp: 1,
                    duration: 0,
                    command: "echo hello \\ world".to_string(),
                    paths: Vec::new(),
                }];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
                assert_eq!(output, b": 1:0;echo hello \\ world\n");
            }

            #[test]
            fn escape_newline() {
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
        }

        mod fish {
            use super::{HistoryEntry, ShellFormat, write_entries};

            #[test]
            fn single() {
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
            fn multiple() {
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
            fn single_path() {
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
            fn multiple_paths() {
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
            fn escape_backslash() {
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
            fn escape_newline() {
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
        }
    }

    mod roundtrip {
        use super::{ShellFormat, parse_entries, write_entries};

        mod sh {
            use super::{ShellFormat, parse_entries, write_entries};

            #[test]
            fn backslash() {
                // echo foo \ bar
                let input = b"echo foo \\ bar\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
                assert_eq!(output, input);
            }

            #[test]
            fn double_backslash() {
                // echo foo \\ bar
                let input = b"echo foo \\\\ bar\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
                assert_eq!(output, input);
            }

            #[test]
            fn backslash_a() {
                // echo foo \a bar
                let input = b"echo foo \\a bar\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
                assert_eq!(output, input);
            }

            #[test]
            fn backslash_n() {
                // echo foo \n bar
                let input = b"echo foo \\n bar\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
                assert_eq!(output, input);
            }

            #[test]
            fn multiline() {
                // echo foo\
                // bar\
                // baz
                let input = b"echo foo\\\nbar\\\nbaz\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
                assert_eq!(output, input);
            }

            #[test]
            fn multiline_with_trailing_backslash() {
                // echo foo\\
                // bar\\
                // baz
                let input = b"echo foo\\\\\nbar\\\\\nbaz\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
                assert_eq!(output, input);
            }
        }

        mod zsh {
            use super::{ShellFormat, parse_entries, write_entries};

            #[test]
            fn backslash() {
                // : 1:0;echo foo \ bar
                let input = b": 1:0;echo foo \\ bar\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
                assert_eq!(output, input);
            }

            #[test]
            fn double_backslash() {
                // : 1:0;echo foo \\ bar
                let input = b": 1:0;echo foo \\\\ hello\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
                assert_eq!(output, input);
            }

            #[test]
            fn multiline() {
                // : 1700000001:0;echo hello\
                // world
                // : 1700000002:5;ls -la
                let input = b": 1700000001:0;echo hello\\\nworld\n: 1700000002:5;ls -la\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
                assert_eq!(output, input);
            }

            #[test]
            fn escaped_newline_colon() {
                // : 100:0;echo foo\
                // : 200:0;echo bar
                let input = b": 100:0;echo foo\\\n: 200:0;echo bar\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
                assert_eq!(output, input);
            }
        }

        mod fish {
            use super::{ShellFormat, parse_entries, write_entries};

            #[test]
            fn simple() {
                // - cmd: echo hello world
                //   when: 1
                let input = b"- cmd: echo hello world\n  when: 1\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
                assert_eq!(output, input);
            }

            #[test]
            fn multiline() {
                // - cmd: echo hello\nworld
                //   when: 1700000001
                // - cmd: ls
                //   when: 1700000002
                let input =
                    b"- cmd: echo hello\\nworld\n  when: 1700000001\n- cmd: ls\n  when: 1700000002\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
                assert_eq!(output, input);
            }

            #[test]
            fn path() {
                // - cmd: cargo build
                //   when: 1700000000
                //   paths:
                //     - ~/Developer/histutils
                // - cmd: ls
                //   when: 1700000001
                let input = b"- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n- cmd: ls\n  when: 1700000001\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
                assert_eq!(output, input);
            }

            #[test]
            fn paths() {
                // - cmd: cargo build
                //   when: 1700000000
                //   paths:
                //     - ~/Developer/histutils
                //     - /tmp
                // - cmd: ls
                //   when: 1700000001
                let input = b"- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n    - /tmp\n- cmd: ls\n  when: 1700000001\n";
                let entries = parse_entries([input.into()]).unwrap().entries;

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
                assert_eq!(output, input);
            }
        }
    }
}
