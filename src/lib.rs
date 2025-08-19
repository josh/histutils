use std::collections::{BTreeMap, HashSet};
use std::io::{BufRead, Cursor, Result as IoResult, Write};

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
    fn from(content: &'a str) -> Self {
        Self {
            reader: Cursor::new(content),
            path: None,
        }
    }
}

impl<'a, const N: usize> From<&'a [u8; N]> for HistoryFile<Cursor<&'a [u8]>> {
    fn from(content: &'a [u8; N]) -> Self {
        Self {
            reader: Cursor::new(content.as_slice()),
            path: None,
        }
    }
}

fn detect_format<R>(reader: &mut R) -> ShellFormat
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

/// Parses history entries from multiple files and fallback timestamp epoch.
///
/// # Arguments
///
/// * `files` - An iterator of `HistoryFile` instances to parse and analyze.
/// * `epoch` - Fallback timestamp epoch to use if no timestamp is found.
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

        // Collect all entries from this file, handling errors
        let mut file_entries = Vec::new();
        match file_format {
            ShellFormat::Fish => {
                for entry_result in parse_fish_entries(&mut reader, &ctx) {
                    file_entries.push(entry_result?);
                }
            }
            ShellFormat::ZshExtended => {
                for entry_result in parse_zsh_extended_entries(&mut reader, &ctx) {
                    file_entries.push(entry_result?);
                }
            }
            ShellFormat::Sh => {
                for entry_result in parse_sh_entries(&mut reader, &ctx) {
                    file_entries.push(entry_result?);
                }
            }
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
    BadFishHeader,
    BadZshExtendedHeader,
    BlankCommand,
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
            ParseError::BadFishHeader => write!(f, "bad fish header"),
            ParseError::BadZshExtendedHeader => write!(f, "bad zsh extended header"),
            ParseError::BlankCommand => write!(f, "blank command"),
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
    ShellHistLines::new(reader).filter_map(move |entry_res| {
        let (line, line_no) = match entry_res {
            Ok((line, line_no)) => (line, line_no),
            Err(e) => return Some(Err(e)),
        };

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

        // Skip blank commands with a warning
        if is_blank_command(&command) {
            if let Some(path) = &ctx.filename {
                eprintln!("{}:{line_no}: skipping blank command", path.display());
            } else {
                eprintln!(":{line_no}: skipping blank command");
            }
            return None;
        }

        Some(Ok(HistoryEntry {
            timestamp: ctx.epoch,
            duration: None,
            command,
            paths: None,
        }))
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

    // Skip blank commands with a warning
    if is_blank_command(&command) {
        if let Some(path) = &ctx.filename {
            eprintln!("{}:{line_no}: skipping blank command", path.display());
        } else {
            eprintln!(":{line_no}: skipping blank command");
        }
        return Err(ParseError::BlankCommand);
    }

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
                eprintln!("{}", String::from_utf8_lossy(&entry_data));
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

    // Skip blank commands with a warning
    if is_blank_command(&command) {
        if let Some(path) = &ctx.filename {
            eprintln!("{}:{line_no}: skipping blank command", path.display());
        } else {
            eprintln!(":{line_no}: skipping blank command");
        }
        return Err(ParseError::BlankCommand);
    }

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

#[must_use]
fn is_blank_command(command: &str) -> bool {
    command.is_empty() || command.chars().all(|c| c == ' ' || c == '\t')
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

fn write_sh_entries<W, I>(writer: &mut W, entries: I) -> IoResult<()>
where
    W: Write,
    I: IntoIterator<Item = HistoryEntry>,
{
    for entry in entries {
        writeln!(writer, "{}", entry.command.replace('\n', "\\\n"))?;
    }
    Ok(())
}

fn write_zsh_entries<W, I>(writer: &mut W, entries: I) -> IoResult<()>
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

fn write_fish_entries<W, I>(writer: &mut W, entries: I) -> IoResult<()>
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

fn merge_history_entries<I>(entries_iterators: I) -> impl Iterator<Item = HistoryEntry>
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
