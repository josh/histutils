use std::collections::{BTreeMap, HashSet};
use std::io::{BufRead, Cursor, Result as IoResult, Write};

use std::fmt;
use std::path::PathBuf;
use std::str;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct HistoryEntry {
    pub timestamp: Option<u64>,
    pub duration: Option<u64>,
    pub command: String,
    pub paths: Option<Vec<String>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ShellFormat {
    Sh,
    ZshExtended,
    Fish,
}

impl fmt::Display for ShellFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            ShellFormat::Sh => "sh",
            ShellFormat::ZshExtended => "zsh",
            ShellFormat::Fish => "fish",
        };
        f.write_str(s)
    }
}

impl ShellFormat {
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::Sh => "sh",
            Self::ZshExtended => "zsh",
            Self::Fish => "fish",
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct Context {
    pub epoch: Option<u64>,
    pub filename: Option<PathBuf>,
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
    parse_entries_with_ctx(files, &Context::default())
}

/// Parses history entries from multiple files and fallback timestamp epoch.
///
/// # Arguments
///
/// * `files` - An iterator of `HistoryFile` instances to parse and analyze.
/// * `epoch` - Fallback timestamp epoch to use if no timestamp is found.
///
/// # Examples
///
/// ```
/// let zsh_history: histutils::HistoryFile<_> = ": 1609459200:5;echo hello\n: 1609459300:2;ls -la\n".into();
/// let bash_history: histutils::HistoryFile<_> = "echo world\nls\n".into();
///
/// let ctx = histutils::Context::default();
/// let history = histutils::parse_entries_with_ctx([zsh_history, bash_history], &ctx).unwrap();
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
pub fn parse_entries_with_ctx<R, I>(files: I, ctx: &Context) -> IoResult<HistoryEntries>
where
    R: BufRead,
    I: IntoIterator<Item = HistoryFile<R>>,
{
    let mut original_formats = HashSet::new();
    let mut entries_iterators = Vec::new();

    for history_file in files {
        let mut ctx = (*ctx).clone();
        ctx.filename = history_file.path.clone();

        let mut reader = history_file.reader;

        let file_format = detect_format(&mut reader);
        original_formats.insert(file_format);

        let entries_iter: Box<dyn Iterator<Item = IoResult<HistoryEntry>>> = match file_format {
            ShellFormat::Fish => Box::new(parse_fish_entries(&mut reader, &ctx)),
            ShellFormat::ZshExtended => Box::new(parse_zsh_extended_entries(&mut reader, &ctx)),
            ShellFormat::Sh => Box::new(parse_sh_entries(&mut reader, &ctx)),
        };

        // Collect all entries from this file, handling errors
        let mut file_entries = Vec::new();
        for entry_result in entries_iter {
            file_entries.push(entry_result?);
        }

        entries_iterators.push(file_entries.into_iter());
    }

    let entries: Vec<_> = merge_history_entries(entries_iterators).collect();

    Ok(HistoryEntries {
        entries,
        original_formats,
    })
}

fn merge_entries(mut a: HistoryEntry, b: HistoryEntry) -> HistoryEntry {
    assert!(
        a.timestamp.is_some() && b.timestamp.is_some(),
        "both entries must have timestamps"
    );
    assert!(
        a.timestamp == b.timestamp,
        "both entries must have the same timestamp"
    );
    assert!(
        a.command == b.command,
        "both entries must have the same command"
    );

    // Prefer non-zero durations, or fall back to any Some duration
    match (a.duration, b.duration) {
        (Some(a_dur), Some(b_dur)) => {
            if a_dur == 0 && b_dur > 0 {
                a.duration = Some(b_dur);
            }
            // Keep a.duration if both are non-zero or if b is zero
        }
        (None, Some(_)) => a.duration = b.duration,
        // Keep a.duration if b is None
        _ => {}
    }

    // Merge paths uniquely
    match (&mut a.paths, b.paths) {
        (None, Some(b_paths)) => a.paths = Some(b_paths),
        (Some(a_paths), Some(b_paths)) => {
            for p in b_paths {
                if !a_paths.contains(&p) {
                    a_paths.push(p);
                }
            }
        }
        _ => {}
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
    ctx: &'a Context,
) -> impl Iterator<Item = IoResult<HistoryEntry>> + 'a
where
    R: BufRead,
{
    ShellHistLines::new(reader).map(move |entry_res| {
        let (line, line_no) = entry_res?;
        let command = if let Ok(s) = str::from_utf8(&line) {
            s.to_string()
        } else {
            if let Some(path) = &ctx.filename {
                eprintln!("{}:{line_no}: invalid UTF-8", path.display());
            } else {
                eprintln!(":{line_no}: invalid UTF-8");
            }
            let lossy = String::from_utf8_lossy(&line);
            eprintln!("{lossy}");
            lossy.to_string()
        };
        Ok(HistoryEntry {
            timestamp: ctx.epoch,
            duration: None,
            command,
            paths: None,
        })
    })
}

fn parse_zsh_extended_entries<'a, R>(
    reader: &'a mut R,
    ctx: &'a Context,
) -> impl Iterator<Item = IoResult<HistoryEntry>> + 'a
where
    R: BufRead,
{
    ShellHistLines::new(reader).filter_map(move |entry_res| match entry_res {
        Ok((line, line_no)) => match parse_zsh_raw_entry(&line, ctx, line_no) {
            Ok(entry) => Some(Ok(entry)),
            Err(err) => {
                if let Some(path) = &ctx.filename {
                    eprintln!("{}:{line_no}: {err}", path.display());
                } else {
                    eprintln!(":{line_no}: {err}");
                }
                eprintln!("{}", String::from_utf8_lossy(&line));
                None
            }
        },
        Err(err) => Some(Err(err)),
    })
}

fn parse_zsh_raw_entry(
    line: &[u8],
    ctx: &Context,
    line_no: usize,
) -> Result<HistoryEntry, ParseError> {
    // Require space after initial colon (": ") per zsh extended history format
    if !line.starts_with(b": ") {
        return Err(ParseError::BadZshExtendedHeader);
    }

    // Parse timestamp until next ':'
    let rest = &line[2..];
    let Some(idx_colon) = rest.iter().position(|&b| b == b':') else {
        return Err(ParseError::BadZshExtendedHeader);
    };
    let ts_bytes = &rest[..idx_colon];
    if ts_bytes.is_empty() {
        return Err(ParseError::BadZshExtendedHeader);
    }

    // Parse duration until ';'
    let rest2 = &rest[idx_colon + 1..];
    let Some(idx_sc) = rest2.iter().position(|&b| b == b';') else {
        return Err(ParseError::BadZshExtendedHeader);
    };
    let dur_bytes = &rest2[..idx_sc];
    if dur_bytes.is_empty() {
        return Err(ParseError::BadZshExtendedHeader);
    }
    let cmd_bytes = &rest2[idx_sc + 1..];
    if cmd_bytes.is_empty() {
        return Err(ParseError::BadZshExtendedHeader);
    }

    let ts_str = str::from_utf8(ts_bytes)?;
    let dur_str = str::from_utf8(dur_bytes)?;
    let timestamp = Some(ts_str.parse()?);
    let duration = Some(dur_str.parse()?);

    let command = if let Ok(s) = str::from_utf8(cmd_bytes) {
        s.to_string()
    } else {
        if let Some(path) = &ctx.filename {
            eprintln!("{}:{line_no}: invalid UTF-8", path.display());
        } else {
            eprintln!(":{line_no}: invalid UTF-8");
        }
        let lossy = String::from_utf8_lossy(cmd_bytes);
        eprintln!("{lossy}");
        lossy.to_string()
    };

    assert!(!command.is_empty(), "command is required");
    assert!(timestamp.is_some(), "timestamp is required");
    assert!(duration.is_some(), "duration is required");

    Ok(HistoryEntry {
        timestamp,
        duration,
        command,
        paths: None,
    })
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
    ctx: &'a Context,
) -> impl Iterator<Item = IoResult<HistoryEntry>> + 'a
where
    R: BufRead,
{
    FishHistEntries::new(reader).filter_map(move |entry_res| match entry_res {
        Ok((entry_data, line_no)) => match parse_fish_raw_entry(&entry_data, ctx, line_no) {
            Ok(entry) => Some(Ok(entry)),
            Err(err) => {
                if let Some(path) = &ctx.filename {
                    eprintln!("{}:{line_no}: {err}", path.display());
                } else {
                    eprintln!(":{line_no}: {err}");
                }
                None
            }
        },
        Err(err) => Some(Err(err)),
    })
}

fn parse_fish_raw_entry(
    data: &[u8],
    ctx: &Context,
    line_no: usize,
) -> Result<HistoryEntry, ParseError> {
    let lines: Vec<&[u8]> = data.split(|&b| b == b'\n').collect();

    if lines.is_empty() {
        return Err(ParseError::BadFishHeader);
    }

    let Some(cmd_bytes) = lines[0].strip_prefix(b"- cmd:") else {
        return Err(ParseError::BadFishHeader);
    };
    let cmd_bytes = cmd_bytes.strip_prefix(b" ").unwrap_or(cmd_bytes);
    let command = if let Ok(s) = str::from_utf8(cmd_bytes) {
        unescape_fish(s)
    } else {
        if let Some(path) = &ctx.filename {
            eprintln!("{}:{line_no}: invalid UTF-8", path.display());
        } else {
            eprintln!(":{line_no}: invalid UTF-8");
        }
        let lossy = String::from_utf8_lossy(cmd_bytes);
        eprintln!("{lossy}");
        unescape_fish(&lossy)
    };

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
        timestamp: Some(timestamp),
        duration: None,
        command,
        paths: if paths.is_empty() { None } else { Some(paths) },
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
///         timestamp: Some(1640995200),
///         duration: Some(1000),
///         command: "ls -la".to_string(),
///         paths: Some(vec!["/home/user".to_string()]),
///     },
///     histutils::HistoryEntry {
///         timestamp: Some(1640995260),
///         duration: Some(500),
///         command: "git status".to_string(),
///         paths: Some(vec!["/home/user/project".to_string()]),
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
/// Returns an error if writing to the output fails or if any entry has a `None` timestamp,
/// as zsh format requires timestamps.
pub fn write_zsh_entries<W, I>(writer: &mut W, entries: I) -> IoResult<()>
where
    W: Write,
    I: IntoIterator<Item = HistoryEntry>,
{
    for entry in entries {
        let timestamp = entry.timestamp.ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "entry missing required timestamp",
            )
        })?;
        writeln!(
            writer,
            ": {}:{};{}",
            timestamp,
            entry.duration.unwrap_or(0),
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
/// Returns an error if writing to the output fails or if any entry has a `None` timestamp,
/// as fish format requires timestamps.
///
/// # Panics
///
/// Panics if paths is `Some` but empty, which should not happen in normal usage.
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
        let timestamp = entry.timestamp.ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "entry missing required timestamp",
            )
        })?;
        writeln!(writer, "  when: {timestamp}")?;
        if let Some(paths) = &entry.paths {
            assert!(!paths.is_empty(), "paths was some but empty");
            writeln!(writer, "  paths:")?;
            for p in paths {
                writeln!(writer, "    - {}", &p)?;
            }
        }
    }
    Ok(())
}

/// Merges multiple iterators of history entries into a single iterator.
///
/// This function takes iterators of `HistoryEntry` and merges them based on timestamp and command.
/// Entries with the same timestamp and command are merged using the `merge_entries` function.
/// Entries without timestamps are never merged and are kept as-is.
///
/// # Arguments
///
/// * `entries_iterators` - An iterator of iterators, where each inner iterator yields `HistoryEntry`
///
/// # Returns
///
/// An iterator over merged `HistoryEntry` items.
///
/// # Examples
///
/// ```
/// use histutils::{HistoryEntry, merge_history_entries};
///
/// let entries1 = vec![
///     HistoryEntry { timestamp: Some(1000), command: "echo hello".to_string(), ..Default::default() },
///     HistoryEntry { timestamp: Some(2000), command: "ls".to_string(), ..Default::default() },
/// ];
///
/// let entries2 = vec![
///     HistoryEntry { timestamp: Some(1000), command: "echo hello".to_string(), ..Default::default() },
///     HistoryEntry { timestamp: Some(3000), command: "pwd".to_string(), ..Default::default() },
/// ];
///
/// let merged: Vec<_> = merge_history_entries(vec![entries1.into_iter(), entries2.into_iter()]).collect();
/// assert_eq!(merged.len(), 3); // 1000:echo hello (merged), 2000:ls, 3000:pwd
/// ```
pub fn merge_history_entries<I>(entries_iterators: I) -> impl Iterator<Item = HistoryEntry>
where
    I: IntoIterator,
    I::Item: IntoIterator<Item = HistoryEntry>,
{
    let mut map: BTreeMap<Option<u64>, Vec<HistoryEntry>> = BTreeMap::new();

    for entries_iter in entries_iterators {
        for entry in entries_iter {
            let entries = map.entry(entry.timestamp).or_default();

            // Never merge entries with missing timestamps
            if entry.timestamp.is_none() {
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

    map.into_iter().flat_map(|(_, v)| v)
}

#[cfg(test)]
mod tests {
    mod detect_format {
        use crate::{ShellFormat, detect_format};
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

    mod parse_sh_entries {
        use crate::{Context, parse_sh_entries};
        use std::{io::Cursor, path::PathBuf};

        #[test]
        fn empty() {
            let mut input = Cursor::new("");
            let path = PathBuf::from(".history");
            let ctx = Context {
                epoch: None,
                filename: Some(path.clone()),
            };
            let mut entries = parse_sh_entries(&mut input, &ctx);
            assert!(entries.next().is_none());
        }

        #[test]
        fn multiple() {
            let mut input = Cursor::new("foo\nbar\nbaz\n");
            let path = PathBuf::from(".history");
            let ctx = Context {
                epoch: None,
                filename: Some(path.clone()),
            };
            let mut entries = parse_sh_entries(&mut input, &ctx);
            assert_eq!("foo", entries.next().unwrap().unwrap().command);
            assert_eq!("bar", entries.next().unwrap().unwrap().command);
            assert_eq!("baz", entries.next().unwrap().unwrap().command);
            assert!(entries.next().is_none());
        }

        #[test]
        fn epoch() {
            let mut input = Cursor::new("foo\nbar\nbaz\n");
            let path = PathBuf::from(".history");
            let ctx = Context {
                epoch: Some(1_234_567_890),
                filename: Some(path.clone()),
            };
            let mut entries = parse_sh_entries(&mut input, &ctx);
            let entry = entries.next().unwrap().unwrap();
            assert_eq!("foo", entry.command);
            assert_eq!(Some(1_234_567_890), entry.timestamp);
        }
    }

    mod parse_zsh_extended_entries {
        use crate::{Context, parse_zsh_extended_entries};
        use std::{io::Cursor, path::PathBuf};

        #[test]
        fn empty() {
            let mut input = Cursor::new("");
            let path = PathBuf::from(".zsh_history");
            let ctx = Context {
                epoch: None,
                filename: Some(path.clone()),
            };
            let mut entries = parse_zsh_extended_entries(&mut input, &ctx);
            assert!(entries.next().is_none());
        }

        #[test]
        fn multiple() {
            let mut input = Cursor::new(": 1:0;foo\n: 2:0;bar\n: 3:0;baz\n");
            let path = PathBuf::from(".zsh_history");
            let ctx = Context {
                epoch: None,
                filename: Some(path.clone()),
            };
            let mut entries = parse_zsh_extended_entries(&mut input, &ctx);
            assert_eq!("foo", entries.next().unwrap().unwrap().command);
            assert_eq!("bar", entries.next().unwrap().unwrap().command);
            assert_eq!("baz", entries.next().unwrap().unwrap().command);
            assert!(entries.next().is_none());
        }
    }

    mod parse_entries {
        use crate::{HistoryFile, parse_entries};

        mod sh {
            use crate::{HistoryFile, parse_entries};

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
                assert_eq!(entries[0].timestamp, None);
                assert_eq!(entries[1].timestamp, None);
                assert_eq!(entries[0].command, "echo hi");
                assert_eq!(entries[1].command, "echo hi");
            }
        }

        mod zsh {
            use crate::{HistoryFile, parse_entries};

            #[test]
            fn multiline() {
                let input: HistoryFile<_> =
                    ": 1700000001:0;echo hello\n: 1700000002:5;ls -la\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 2);

                assert_eq!(entries[0].timestamp, Some(1_700_000_001));
                assert_eq!(entries[0].duration, Some(0));
                assert_eq!(entries[0].command, "echo hello");

                assert_eq!(entries[1].timestamp, Some(1_700_000_002));
                assert_eq!(entries[1].duration, Some(5));
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
                assert_eq!(entries[0].timestamp, Some(1));
                assert_eq!(entries[1].timestamp, Some(2));
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
                assert_eq!(entries[0].timestamp, Some(1));
                assert_eq!(entries[0].command, "one");
            }
        }

        mod fish {
            use crate::{HistoryFile, parse_entries};

            #[test]
            fn single() {
                let input: HistoryFile<_> = "- cmd: cargo build\n  when: 1700000000\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].timestamp, Some(1_700_000_000));
                assert_eq!(entries[0].command, "cargo build");
            }

            #[test]
            fn paths_single() {
                let input: HistoryFile<_> =
                    "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/Developer/histutils\n"
                        .into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 1);
                assert_eq!(
                    entries[0].paths,
                    Some(vec!["~/Developer/histutils".to_string()])
                );
            }

            #[test]
            fn paths_multiple() {
                let input: HistoryFile<_> = "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/project1\n    - ~/project2\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 1);
                assert_eq!(
                    entries[0].paths,
                    Some(vec!["~/project1".to_string(), "~/project2".to_string()])
                );
            }

            #[test]
            fn paths_then_new_entry() {
                let input: HistoryFile<_> = "- cmd: cargo build\n  when: 1700000000\n  paths:\n    - ~/project1\n- cmd: echo hi\n  when: 1700000001\n".into();
                let entries = parse_entries([input]).unwrap().entries;

                assert_eq!(entries.len(), 2);
                assert_eq!(entries[0].paths, Some(vec!["~/project1".to_string()]));
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
                assert_eq!(entries[0].timestamp, Some(1_516_464_765));
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
                assert_eq!(entry.timestamp, Some(1000));
                assert_eq!(entry.command, "echo hello");
                assert_eq!(entry.duration, Some(5));
                assert_eq!(entry.paths, Some(vec!["/tmp".to_string()]));
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
            assert_eq!(entries[0].timestamp, None);
            assert_eq!(entries[1].timestamp, Some(1));
            assert_eq!(entries[2].timestamp, Some(2));
        }
    }

    mod merge_history_entries {
        use crate::{HistoryEntry, merge_history_entries};

        #[test]
        fn merge_duplicate_entries() {
            let entries1 = vec![
                HistoryEntry {
                    timestamp: Some(1000),
                    duration: Some(5),
                    command: "echo hello".to_string(),
                    paths: Some(vec!["/tmp".to_string()]),
                },
                HistoryEntry {
                    timestamp: Some(2000),
                    duration: Some(10),
                    command: "ls".to_string(),
                    paths: None,
                },
            ];

            let entries2 = vec![
                HistoryEntry {
                    timestamp: Some(1000),
                    duration: Some(0),
                    command: "echo hello".to_string(),
                    paths: Some(vec!["/home".to_string()]),
                },
                HistoryEntry {
                    timestamp: Some(3000),
                    duration: Some(15),
                    command: "pwd".to_string(),
                    paths: None,
                },
            ];

            let merged: Vec<_> =
                merge_history_entries(vec![entries1.into_iter(), entries2.into_iter()]).collect();

            assert_eq!(merged.len(), 3);

            // Check that the duplicate entry was merged correctly
            let echo_entry = merged.iter().find(|e| e.command == "echo hello").unwrap();
            assert_eq!(echo_entry.timestamp, Some(1000));
            assert_eq!(echo_entry.duration, Some(5)); // Prefer non-zero duration
            assert_eq!(
                echo_entry.paths,
                Some(vec!["/tmp".to_string(), "/home".to_string()])
            );

            // Check other entries are preserved
            assert!(
                merged
                    .iter()
                    .any(|e| e.command == "ls" && e.timestamp == Some(2000))
            );
            assert!(
                merged
                    .iter()
                    .any(|e| e.command == "pwd" && e.timestamp == Some(3000))
            );
        }

        #[test]
        fn preserve_entries_without_timestamps() {
            let entries1 = vec![HistoryEntry {
                timestamp: None,
                duration: None,
                command: "echo hello".to_string(),
                paths: None,
            }];

            let entries2 = vec![HistoryEntry {
                timestamp: None,
                duration: None,
                command: "echo hello".to_string(),
                paths: None,
            }];

            let merged: Vec<_> =
                merge_history_entries(vec![entries1.into_iter(), entries2.into_iter()]).collect();

            // Entries without timestamps should never be merged
            assert_eq!(merged.len(), 2);
            assert_eq!(
                merged.iter().filter(|e| e.command == "echo hello").count(),
                2
            );
        }

        #[test]
        fn empty_iterators() {
            let merged: Vec<_> =
                merge_history_entries::<Vec<std::iter::Empty<HistoryEntry>>>(vec![]).collect();
            assert_eq!(merged.len(), 0);
        }
    }

    mod write_entries {
        mod sh {
            use crate::{HistoryEntry, ShellFormat, write_entries};

            #[test]
            fn single() {
                let entries = vec![HistoryEntry {
                    timestamp: None,
                    duration: None,
                    command: "echo hello".to_string(),
                    paths: None,
                }];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
                assert_eq!(output, b"echo hello\n");
            }

            #[test]
            fn multiple() {
                let entries = vec![
                    HistoryEntry {
                        timestamp: None,
                        duration: None,
                        command: "echo foo".to_string(),
                        paths: None,
                    },
                    HistoryEntry {
                        timestamp: None,
                        duration: None,
                        command: "echo bar".to_string(),
                        paths: None,
                    },
                ];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
                assert_eq!(output, b"echo foo\necho bar\n");
            }

            #[test]
            fn no_escape_backslash() {
                let entries = vec![HistoryEntry {
                    timestamp: None,
                    duration: None,
                    command: "echo hello \\ world".to_string(),
                    paths: None,
                }];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
                assert_eq!(output, b"echo hello \\ world\n");
            }

            #[test]
            fn escape_newline() {
                let entries = vec![HistoryEntry {
                    timestamp: None,
                    duration: None,
                    command: "echo hello\nworld".to_string(),
                    paths: None,
                }];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Sh).unwrap();
                assert_eq!(output, b"echo hello\\\nworld\n");
            }
        }

        mod zsh {
            use crate::{HistoryEntry, ShellFormat, write_entries};

            #[test]
            fn single() {
                let entries = vec![HistoryEntry {
                    timestamp: Some(1),
                    duration: Some(0),
                    command: "echo hello".to_string(),
                    paths: None,
                }];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
                assert_eq!(output, b": 1:0;echo hello\n");
            }

            #[test]
            fn multiple() {
                let entries = vec![
                    HistoryEntry {
                        timestamp: Some(1),
                        duration: Some(0),
                        command: "echo foo".to_string(),
                        paths: None,
                    },
                    HistoryEntry {
                        timestamp: Some(2),
                        duration: Some(0),
                        command: "echo bar".to_string(),
                        paths: None,
                    },
                ];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
                assert_eq!(output, b": 1:0;echo foo\n: 2:0;echo bar\n");
            }

            #[test]
            fn no_escape_backslash() {
                let entries = vec![HistoryEntry {
                    timestamp: Some(1),
                    duration: Some(0),
                    command: "echo hello \\ world".to_string(),
                    paths: None,
                }];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
                assert_eq!(output, b": 1:0;echo hello \\ world\n");
            }

            #[test]
            fn escape_newline() {
                let entries = vec![HistoryEntry {
                    timestamp: Some(1),
                    duration: Some(0),
                    command: "echo hello\nworld".to_string(),
                    paths: None,
                }];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::ZshExtended).unwrap();
                assert_eq!(output, b": 1:0;echo hello\\\nworld\n");
            }
            #[test]
            fn missing_timestamp_error() {
                let entries = vec![HistoryEntry {
                    timestamp: None,
                    duration: Some(0),
                    command: "echo hello".to_string(),
                    paths: None,
                }];

                let mut output = Vec::new();
                let result = write_entries(&mut output, entries, ShellFormat::ZshExtended);
                assert!(result.is_err());
                let err = result.unwrap_err();
                assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
                assert_eq!(err.to_string(), "entry missing required timestamp");
            }
        }

        mod fish {
            use crate::{HistoryEntry, ShellFormat, write_entries};

            #[test]
            fn single() {
                let entries = vec![HistoryEntry {
                    timestamp: Some(1),
                    duration: Some(0),
                    command: "echo hello".to_string(),
                    paths: None,
                }];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
                assert_eq!(output, b"- cmd: echo hello\n  when: 1\n");
            }

            #[test]
            fn multiple() {
                let entries = vec![
                    HistoryEntry {
                        timestamp: Some(1),
                        duration: Some(0),
                        command: "echo foo".to_string(),
                        paths: None,
                    },
                    HistoryEntry {
                        timestamp: Some(2),
                        duration: Some(0),
                        command: "echo bar".to_string(),
                        paths: None,
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
                    timestamp: Some(1_700_000_000),
                    duration: Some(100),
                    command: "cargo build".to_string(),
                    paths: Some(vec!["~/Developer/histutils".to_string()]),
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
                    timestamp: Some(1_700_000_000),
                    duration: Some(100),
                    command: "cargo build".to_string(),
                    paths: Some(vec![
                        "~/Developer/histutils".to_string(),
                        "/tmp".to_string(),
                    ]),
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
                    timestamp: Some(1),
                    duration: Some(0),
                    command: "echo hello \\ world".to_string(),
                    paths: None,
                }];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
                assert_eq!(output, b"- cmd: echo hello \\\\ world\n  when: 1\n");
            }

            #[test]
            fn escape_newline() {
                let entries = vec![HistoryEntry {
                    timestamp: Some(1),
                    duration: Some(0),
                    command: "echo hello\nworld".to_string(),
                    paths: None,
                }];

                let mut output = Vec::new();
                write_entries(&mut output, entries, ShellFormat::Fish).unwrap();
                assert_eq!(output, b"- cmd: echo hello\\nworld\n  when: 1\n");
            }

            #[test]
            fn missing_timestamp_error() {
                let entries = vec![HistoryEntry {
                    timestamp: None,
                    duration: Some(0),
                    command: "echo hello".to_string(),
                    paths: None,
                }];

                let mut output = Vec::new();
                let result = write_entries(&mut output, entries, ShellFormat::Fish);
                assert!(result.is_err());
                let err = result.unwrap_err();
                assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
                assert_eq!(err.to_string(), "entry missing required timestamp");
            }
        }
    }

    mod roundtrip {
        mod sh {
            use crate::{ShellFormat, parse_entries, write_entries};

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
            use crate::{ShellFormat, parse_entries, write_entries};

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
            use crate::{ShellFormat, parse_entries, write_entries};

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
