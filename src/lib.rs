use std::collections::{BTreeMap, HashSet};
use std::io::{self, BufRead, Cursor, Read, Result as IoResult, Write};

use std::path::PathBuf;
use std::str;

const DISTANT_FUTURE: u64 = 4_102_444_800;
const MAX_COMMAND_LENGTH: usize = 1024; // 1KB limit

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct HistoryEntry {
    pub timestamp: Option<u64>,
    pub added_when: Option<u64>,
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
            Self::ZshExtended => "zsh-extended",
            Self::Fish => "fish",
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct Context {
    pub filename: Option<PathBuf>,
    pub fix: bool,
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
        if self.original_formats.is_empty() {
            return Some(ShellFormat::Sh);
        }
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

fn detect_format<R>(reader: &mut R) -> IoResult<(Option<ShellFormat>, Vec<u8>)>
where
    R: BufRead,
{
    let mut prefix = Vec::new();
    let mut saw_comment = false;
    loop {
        let line_start = prefix.len();
        if reader.read_until(b'\n', &mut prefix)? == 0 {
            let format = saw_comment.then_some(ShellFormat::Sh);
            return Ok((format, prefix));
        }
        let line = prefix[line_start..]
            .strip_suffix(b"\n")
            .unwrap_or(&prefix[line_start..]);
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if line.starts_with(b"#") {
            saw_comment = true;
            continue;
        }
        if line.iter().all(u8::is_ascii_whitespace) {
            continue;
        }
        if line.starts_with(b"- cmd:") {
            return Ok((Some(ShellFormat::Fish), prefix));
        }
        if let Some(header) = line.strip_prefix(b": ") {
            if header
                .first()
                .is_some_and(|byte| byte.is_ascii_digit() || matches!(byte, b'-' | b':'))
            {
                return Ok((Some(ShellFormat::ZshExtended), prefix));
            }
        }
        return Ok((Some(ShellFormat::Sh), prefix));
    }
}

/// Parses history entries from multiple files.
///
/// # Arguments
///
/// * `files` - An iterator of `HistoryFile` instances to parse and analyze.
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
        ctx.filename.clone_from(&history_file.path);

        let mut reader = history_file.reader;

        let (file_format, prefix) = detect_format(&mut reader)?;
        let mut reader = Cursor::new(prefix).chain(reader);
        if let Some(file_format) = file_format {
            original_formats.insert(file_format);
        }

        // Collect all entries from this file, handling errors
        let mut file_entries = Vec::new();
        match file_format.unwrap_or(ShellFormat::Sh) {
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

        if ctx.fix {
            for entry in &mut file_entries {
                fix_command(entry, &ctx);
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
        a.command == b.command,
        "both entries must have the same command"
    );

    let a_first_added = a.added_when.or(a.timestamp);
    let b_first_added = b.added_when.or(b.timestamp);
    assert!(
        a.timestamp == b.timestamp || a_first_added == b_first_added,
        "entries must have the same timestamp or first-added time"
    );

    if a.timestamp == b.timestamp {
        // Prefer non-zero durations, or fall back to any Some duration.
        match (a.duration, b.duration) {
            (Some(0), Some(b_dur)) if b_dur > 0 => a.duration = Some(b_dur),
            (None, Some(_)) => a.duration = b.duration,
            _ => {}
        }
    } else if b.timestamp > a.timestamp {
        a.duration = b.duration;
    }

    a.timestamp = a.timestamp.max(b.timestamp);
    a.added_when = match (a_first_added, b_first_added) {
        (Some(a_time), Some(b_time)) => Some(a_time.min(b_time)),
        (time @ Some(_), None) | (None, time @ Some(_)) => time,
        (None, None) => None,
    };
    if a.added_when == a.timestamp {
        a.added_when = None;
    }

    // Prefer non-empty paths from either side; if both have paths, keep `a`'s.
    a.paths = match (a.paths.take(), b.paths) {
        (Some(a_paths), Some(b_paths)) => {
            if a_paths.is_empty() && !b_paths.is_empty() {
                Some(b_paths)
            } else if a_paths.is_empty() && b_paths.is_empty() {
                None
            } else {
                Some(a_paths)
            }
        }
        (Some(a_paths), None) => {
            if a_paths.is_empty() {
                None
            } else {
                Some(a_paths)
            }
        }
        (None, Some(b_paths)) => {
            if b_paths.is_empty() {
                None
            } else {
                Some(b_paths)
            }
        }
        (None, None) => None,
    };

    a
}

enum ParseError {
    BadFishHeader,
    BadZshExtendedHeader,
    BlankCommand,
    FutureTimestamp,
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
            ParseError::BlankCommand => write!(f, "skipping blank command"),
            ParseError::FutureTimestamp => write!(f, "skipping distant future timestamp"),
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
            Ok(_) => {
                if self.buf.ends_with(b"\r\n") {
                    self.buf.remove(self.buf.len() - 2);
                }
                Some(Ok((self.buf.clone(), self.line_no)))
            }
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

fn print_entry<E: std::fmt::Display>(ctx: &Context, line_no: usize, msg: E, entry: &[u8]) {
    if let Some(path) = &ctx.filename {
        eprintln!("{}:{line_no}: {msg}", path.display());
    } else {
        eprintln!(":{line_no}: {msg}");
    }
    let mut stderr = io::stderr();
    let _ = stderr.write_all(entry);
    if !entry.ends_with(b"\n") {
        let _ = stderr.write_all(b"\n");
    }
}

fn fix_command(entry: &mut HistoryEntry, ctx: &Context) {
    let mut fixed = false;
    // Corruption can nest (a corrupted entry re-corrupted on a later write),
    // so keep stripping headers until the command is clean.
    while let Some(fixed_entry) = extract_corrupted_entity(entry) {
        *entry = fixed_entry;
        fixed = true;
    }
    if fixed {
        eprintln!(
            "{}: fixing corrupted header in command",
            if let Some(path) = &ctx.filename {
                format!("{}", path.display())
            } else {
                "stdin".to_string()
            }
        );
    }
}

fn extract_corrupted_entity(entry: &HistoryEntry) -> Option<HistoryEntry> {
    let rest = entry.command.strip_prefix(": ")?;
    let idx_colon = rest.find(':')?;
    let ts_part = &rest[..idx_colon];
    if ts_part.is_empty() || !ts_part.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let rest2 = &rest[idx_colon + 1..];
    let idx_sc = rest2.find(';')?;
    let dur_part = &rest2[..idx_sc];
    if dur_part.is_empty() || !dur_part.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let new_command = rest2[idx_sc + 1..].to_string();

    let embedded_ts: u64 = ts_part.parse().ok()?;
    let embedded_dur: u64 = dur_part.parse().ok()?;

    if embedded_ts > DISTANT_FUTURE {
        return None;
    }

    let mut fixed_entry = entry.clone();
    fixed_entry.command = new_command;

    // Adopt the embedded metadata for zsh entries (whose own header was the
    // corrupted duplicate) and for entries with no timestamp of their own
    // (sh input), where the embedded header is the only record of when the
    // command ran. Fish entries keep their own `when` timestamp.
    if entry.duration.is_some() || entry.timestamp.is_none() {
        fixed_entry.timestamp = Some(embedded_ts);
        fixed_entry.duration = Some(embedded_dur);
    }

    Some(fixed_entry)
}

fn truncate_command(command: &mut String, ctx: &Context, line_no: usize, raw_entry: &[u8]) {
    if command.len() > MAX_COMMAND_LENGTH {
        print_entry(
            ctx,
            line_no,
            format!(
                "command truncated from {} bytes to {} bytes",
                command.len(),
                MAX_COMMAND_LENGTH
            ),
            raw_entry,
        );
        let mut truncated = String::with_capacity(MAX_COMMAND_LENGTH);
        for ch in command.chars() {
            let ch_len = ch.len_utf8();
            if truncated.len() + ch_len > MAX_COMMAND_LENGTH {
                break;
            }
            truncated.push(ch);
        }
        *command = truncated;
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

        let mut command = if let Ok(s) = str::from_utf8(&line) {
            if s.contains('\0') {
                print_entry(ctx, line_no, "invalid null byte", &line);
                s.replace('\0', "�")
            } else {
                s.to_string()
            }
        } else {
            print_entry(ctx, line_no, "invalid UTF-8", &line);
            let lossy = String::from_utf8_lossy(&line);
            if lossy.contains('\0') {
                print_entry(ctx, line_no, "invalid null byte", &line);
                lossy.replace('\0', "�")
            } else {
                lossy.to_string()
            }
        };

        truncate_command(&mut command, ctx, line_no, &line);

        if is_blank_command(&command) {
            print_entry(ctx, line_no, "skipping blank command", &line);
            return None;
        }

        debug_assert!(
            !command.contains('\0'),
            "HistoryEntry command must not contain null bytes"
        );
        Some(Ok(HistoryEntry {
            timestamp: None,
            added_when: None,
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
                print_entry(ctx, line_no, err, &line);
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
    let ts_val: u64 = ts_str.parse()?;
    if ts_val > DISTANT_FUTURE {
        return Err(ParseError::FutureTimestamp);
    }
    let timestamp = Some(ts_val);
    let duration = Some(dur_str.parse()?);

    let mut command = if let Ok(s) = str::from_utf8(cmd_bytes) {
        if s.contains('\0') {
            print_entry(ctx, line_no, "invalid null byte", line);
            s.replace('\0', "�")
        } else {
            s.to_string()
        }
    } else {
        print_entry(ctx, line_no, "invalid UTF-8", line);
        let lossy = String::from_utf8_lossy(cmd_bytes);
        if lossy.contains('\0') {
            print_entry(ctx, line_no, "invalid null byte", line);
            lossy.replace('\0', "�")
        } else {
            lossy.to_string()
        }
    };

    truncate_command(&mut command, ctx, line_no, line);

    if is_blank_command(&command) {
        return Err(ParseError::BlankCommand);
    }

    assert!(timestamp.is_some(), "timestamp is required");
    assert!(duration.is_some(), "duration is required");

    debug_assert!(
        !command.contains('\0'),
        "HistoryEntry command must not contain null bytes"
    );
    Ok(HistoryEntry {
        timestamp,
        added_when: None,
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
                print_entry(ctx, line_no, err, &entry_data);
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
    let mut command = if let Ok(s) = str::from_utf8(cmd_bytes) {
        let unescaped = unescape_fish(s);
        if unescaped.contains('\0') {
            print_entry(ctx, line_no, "invalid null byte", data);
            unescaped.replace('\0', "�")
        } else {
            unescaped
        }
    } else {
        print_entry(ctx, line_no, "invalid UTF-8", data);
        let lossy = String::from_utf8_lossy(cmd_bytes);
        let unescaped = unescape_fish(&lossy);
        if unescaped.contains('\0') {
            print_entry(ctx, line_no, "invalid null byte", data);
            unescaped.replace('\0', "�")
        } else {
            unescaped
        }
    };

    truncate_command(&mut command, ctx, line_no, data);

    if is_blank_command(&command) {
        return Err(ParseError::BlankCommand);
    }

    let mut timestamp = None;
    let mut added_when = None;
    let mut paths: Vec<String> = Vec::new();
    let mut i = 1;
    while i < lines.len() {
        let Some(line) = lines[i].strip_prefix(b"  ") else {
            i += 1;
            continue;
        };
        if let Some(rest) = line.strip_prefix(b"when:") {
            timestamp = Some(parse_fish_timestamp(rest)?);
        } else if let Some(rest) = line.strip_prefix(b"added_when:") {
            added_when = Some(parse_fish_timestamp(rest)?);
        } else if line == b"paths:" {
            i += 1;
            while i < lines.len() {
                let Some(path_line) = lines[i].strip_prefix(b"    ") else {
                    break;
                };
                if path_line.is_empty() {
                    break;
                }
                if let Some(path_bytes) = path_line.strip_prefix(b"- ") {
                    // A path is auxiliary metadata; repair invalid UTF-8
                    // and null bytes like commands instead of dropping the
                    // whole entry.
                    let mut path_str = if let Ok(s) = str::from_utf8(path_bytes) {
                        unescape_fish(s)
                    } else {
                        print_entry(ctx, line_no, "invalid UTF-8", data);
                        unescape_fish(&String::from_utf8_lossy(path_bytes))
                    };
                    if path_str.contains('\0') {
                        print_entry(ctx, line_no, "invalid null byte", data);
                        path_str = path_str.replace('\0', "\u{FFFD}");
                    }
                    paths.push(path_str);
                } else {
                    break;
                }
                i += 1;
            }
            continue;
        }
        i += 1;
    }

    let Some(timestamp) = timestamp else {
        return Err(ParseError::BadFishHeader);
    };

    debug_assert!(
        !command.contains('\0'),
        "HistoryEntry command must not contain null bytes"
    );
    Ok(HistoryEntry {
        timestamp: Some(timestamp),
        added_when,
        duration: None,
        command,
        paths: if paths.is_empty() { None } else { Some(paths) },
    })
}

fn parse_fish_timestamp(value: &[u8]) -> Result<u64, ParseError> {
    let value = value.strip_prefix(b" ").unwrap_or(value);
    let timestamp = str::from_utf8(value)?.parse()?;
    if timestamp > DISTANT_FUTURE {
        return Err(ParseError::FutureTimestamp);
    }
    Ok(timestamp)
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
        // Validate before writing anything so an entry without a timestamp
        // does not leave a dangling partial record in the output.
        let timestamp = entry.timestamp.ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "entry missing required timestamp",
            )
        })?;
        writeln!(
            writer,
            "- cmd: {}",
            entry.command.replace('\\', "\\\\").replace('\n', "\\n")
        )?;
        writeln!(writer, "  when: {timestamp}")?;
        if let Some(added_when) = entry.added_when.filter(|&time| time != timestamp) {
            writeln!(writer, "  added_when: {added_when}")?;
        }
        if let Some(paths) = &entry.paths {
            assert!(!paths.is_empty(), "paths was some but empty");
            writeln!(writer, "  paths:")?;
            for p in paths {
                write!(writer, "    - ")?;
                write_fish_escaped(writer, p)?;
                writeln!(writer)?;
            }
        }
    }
    Ok(())
}

fn write_fish_escaped<W: Write>(writer: &mut W, value: &str) -> IoResult<()> {
    for part in value.split_inclusive(['\\', '\n']) {
        if let Some(value) = part.strip_suffix('\\') {
            write!(writer, "{value}\\\\")?;
        } else if let Some(value) = part.strip_suffix('\n') {
            write!(writer, "{value}\\n")?;
        } else {
            write!(writer, "{part}")?;
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

    let mut modern_map: BTreeMap<Option<u64>, Vec<(usize, HistoryEntry)>> = BTreeMap::new();
    for (position, entry) in map.into_values().flatten().enumerate() {
        let first_added = entry.added_when.or(entry.timestamp);
        let entries = modern_map.entry(first_added).or_default();
        if let Some((existing_position, existing)) = entries.iter_mut().find(|(_, item)| {
            (entry.added_when.is_some() || item.added_when.is_some())
                && item.command == entry.command
        }) {
            if entry.timestamp > existing.timestamp {
                *existing_position = position;
            } else if entry.timestamp == existing.timestamp {
                *existing_position = (*existing_position).min(position);
            }
            *existing = merge_entries(existing.clone(), entry);
            continue;
        }
        entries.push((position, entry));
    }

    let mut entries: Vec<_> = modern_map.into_values().flatten().collect();
    entries.sort_by_key(|(position, entry)| (entry.timestamp, *position));
    entries.into_iter().map(|(_, entry)| entry)
}
