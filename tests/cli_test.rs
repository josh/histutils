use std::io::Write;
use std::path::PathBuf;
use std::process::{self, Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static COUNTER: AtomicU64 = AtomicU64::new(0);

/// Helper struct for creating temporary test files that are automatically cleaned up
struct TempFile {
    path: PathBuf,
}

impl TempFile {
    /// Creates a new temporary file with the given content
    fn with_content(content: &str) -> Self {
        let temp_dir = std::env::temp_dir();
        let pid = u128::from(process::id()); // 32 bits on all tier-1 platforms
        let n = u128::from(COUNTER.fetch_add(1, Ordering::Relaxed));
        let unique_id = (pid << 96) | n;
        let temp_file = temp_dir.join(format!("histutils_test_{unique_id}"));
        std::fs::write(&temp_file, content).expect("failed to write temp file");

        Self { path: temp_file }
    }

    /// Gets the path as a string slice
    fn path_str(&self) -> &str {
        self.path
            .to_str()
            .expect("temp file path is not valid UTF-8")
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

fn get_bin() -> &'static str {
    env!("CARGO_BIN_EXE_histutils")
}

fn histutils(args: &[&str]) -> std::process::Output {
    Command::new(get_bin())
        .args(args)
        .output()
        .expect("failed to run process")
}

fn histutils_with_stdin(args: &[&str], stdin_content: &[u8]) -> std::process::Output {
    let mut child = Command::new(get_bin())
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn process");

    {
        let stdin = child.stdin.as_mut().expect("failed to open stdin");
        stdin
            .write_all(stdin_content)
            .expect("failed to write to stdin");
    }

    child.wait_with_output().expect("failed to wait on child")
}

// Helper function to get the full path to a test data file
fn test_data_path(name: &str) -> String {
    let project_root = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(project_root)
        .join("tests")
        .join("data")
        .join(name)
        .to_str()
        .expect("test data path is not valid UTF-8")
        .to_string()
}

#[test]
fn prints_help() {
    let output = histutils(&["--help"]);

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let expected_output = "usage: histutils [--output FILE] [--output-format FORMAT] [--count] [--epoch EPOCH] [--version] [FILE...]\n";
    assert_eq!(stdout, expected_output);
}

#[test]
fn prints_version() {
    let output = histutils(&["--version"]);

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);

    let expected_version = env!("CARGO_PKG_VERSION");
    let expected_output = format!("histutils {expected_version}\n");
    assert_eq!(stdout, expected_output);
}

#[test]
fn bad_format() {
    let output = histutils(&["--output-format", "foo"]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(stderr, "usage: unknown --output-format=foo\n");
}

#[test]
fn missing_epoch_value() {
    let output = histutils(&["--epoch"]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(stderr, "usage: --epoch requires a value\n");
}

#[test]
fn count_stdin() {
    let output = histutils_with_stdin(&["--count"], b"foo\nbar\nbaz\n");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "3");
}

#[test]
fn writes_to_output_file() {
    let input_str = ": 123:0;echo hello\n";
    let input_file = TempFile::with_content(input_str);
    let output_file = TempFile::with_content("");

    let output = histutils(&["--output", output_file.path_str(), input_file.path_str()]);

    assert!(output.status.success());
    assert!(output.stdout.is_empty());

    let output_str =
        std::fs::read_to_string(&output_file.path).expect("failed to read output file");
    assert_eq!(output_str, input_str);
}

#[test]
fn overwrites_existing_output_file() {
    let input_str = ": 123:0;echo hello\n";
    let input_file = TempFile::with_content(input_str);
    let output_file = TempFile::with_content("initial contents\n");

    let output = histutils(&["--output", output_file.path_str(), input_file.path_str()]);

    assert!(output.status.success());
    assert!(output.stdout.is_empty());

    let output_str =
        std::fs::read_to_string(&output_file.path).expect("failed to read output file");
    assert_eq!(output_str, input_str);
}

#[test]
fn count_zsh_history() {
    let data_file = test_data_path("zsh_common_history");

    let output = histutils(&["--count", &data_file]);

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "10");
}

#[test]
fn reads_fish_history() {
    let data_file = test_data_path("fish_common_history");

    let output = histutils(&["--count", &data_file]);

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "10");
}

#[test]
fn reads_sh_history() {
    let data_file = test_data_path("sh_history");

    let output = histutils(&["--count", &data_file]);

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "10");
}

#[test]
fn sh_invalid_utf8_handling() {
    let output = histutils_with_stdin(&["--count"], b"echo hello\xFF\nok\n");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "2");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(stderr, ":1: invalid UTF-8\necho hello\u{FFFD}\n");
}

#[test]
fn zsh_invalid_utf8_handling() {
    let output = histutils_with_stdin(&["--count"], b": 123:0;echo hello\xFF\n: 124:0;ok\n");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "2");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(stderr, ":1: invalid UTF-8\necho hello\u{FFFD}\n");
}

#[test]
fn fish_invalid_utf8_handling() {
    let output = histutils_with_stdin(
        &["--count"],
        b"- cmd: echo hello\xFF\n  when: 123\n- cmd: ok\n  when: 124\n",
    );

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "2");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(stderr, ":1: invalid UTF-8\necho hello\u{FFFD}\n");
}

#[test]
fn roundtrip_sh_history() {
    let data_file = test_data_path("sh_history");
    let input_str = std::fs::read_to_string(&data_file).expect("failed to read file");

    let output = histutils(&["--output-format", "sh", &data_file]);
    let output_str = String::from_utf8(output.stdout).expect("failed to convert to string");

    assert!(output.status.success());
    assert_eq!(output_str, input_str);
}

#[test]
fn roundtrip_zsh_common_history() {
    let data_file = test_data_path("zsh_common_history");
    let input_str = std::fs::read_to_string(&data_file).expect("failed to read file");

    let output = histutils(&["--output-format", "zsh", &data_file]);
    let output_str = String::from_utf8(output.stdout).expect("failed to convert to string");

    assert!(output.status.success());
    assert_eq!(output_str, input_str);
}

#[test]
fn roundtrip_zsh_duration_history() {
    let data_file = test_data_path("zsh_duration_history");
    let input_str = std::fs::read_to_string(&data_file).expect("failed to read file");

    let output = histutils(&["--output-format", "zsh", &data_file]);
    let output_str = String::from_utf8(output.stdout).expect("failed to convert to string");

    assert!(output.status.success());
    assert_eq!(output_str, input_str);
}

#[test]
fn roundtrip_fish_common_history() {
    let data_file = test_data_path("fish_common_history");
    let input_str = std::fs::read_to_string(&data_file).expect("failed to read file");

    let output = histutils(&["--output-format", "fish", &data_file]);
    let output_str = String::from_utf8(output.stdout).expect("failed to convert to string");

    assert!(output.status.success());
    assert_eq!(output_str, input_str);
}

#[test]
fn roundtrip_fish_paths_history() {
    let data_file = test_data_path("fish_paths_history");
    let input_str = std::fs::read_to_string(&data_file).expect("failed to read file");

    let output = histutils(&["--output-format", "fish", &data_file]);
    let output_str = String::from_utf8(output.stdout).expect("failed to convert to string");

    assert!(output.status.success());
    assert_eq!(output_str, input_str);
}

#[test]
fn lossless_zsh_to_fish() {
    let input_data_file = test_data_path("zsh_common_history");
    let output_data_file = test_data_path("fish_common_history");

    let output = histutils(&["--output-format", "fish", &input_data_file]);
    let actual_output_str = String::from_utf8(output.stdout).expect("failed to convert to string");
    let expected_output_str =
        std::fs::read_to_string(&output_data_file).expect("failed to read file");

    assert!(output.status.success());
    assert_eq!(actual_output_str, expected_output_str);
}

#[test]
fn lossless_fish_to_zsh() {
    let input_data_file = test_data_path("fish_common_history");
    let output_data_file = test_data_path("zsh_common_history");

    let output = histutils(&["--output-format", "zsh", &input_data_file]);
    let actual_output_str = String::from_utf8(output.stdout).expect("failed to convert to string");
    let expected_output_str =
        std::fs::read_to_string(&output_data_file).expect("failed to read file");

    assert!(output.status.success());
    assert_eq!(actual_output_str, expected_output_str);
}

#[test]
fn lossy_zsh_to_sh() {
    let input_data_file = test_data_path("zsh_common_history");
    let output_data_file = test_data_path("sh_history");

    let output = histutils(&["--output-format", "sh", &input_data_file]);
    let actual_output_str = String::from_utf8(output.stdout).expect("failed to convert to string");
    let expected_output_str =
        std::fs::read_to_string(&output_data_file).expect("failed to read file");

    assert!(output.status.success());
    assert_eq!(actual_output_str, expected_output_str);
}

#[test]
fn lossy_fish_to_sh() {
    let input_data_file = test_data_path("fish_common_history");
    let output_data_file = test_data_path("sh_history");

    let output = histutils(&["--output-format", "sh", &input_data_file]);
    let actual_output_str = String::from_utf8(output.stdout).expect("failed to convert to string");
    let expected_output_str =
        std::fs::read_to_string(&output_data_file).expect("failed to read file");

    assert!(output.status.success());
    assert_eq!(actual_output_str, expected_output_str);
}

#[test]
fn sh_to_zsh_missing_epoch() {
    let data_file = test_data_path("sh_history");

    let output = histutils(&["--output-format", "zsh", &data_file]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("usage: --epoch="));
    assert!(stderr.contains("required when exporting timestampless entries to zsh"));
}

#[test]
fn zsh_bad_history_count() {
    let data_file = test_data_path("zsh_bad_history");

    let output = histutils(&["--count", &data_file]);

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "1");
}

#[test]
fn zsh_bad_history_to_zsh() {
    let data_file = test_data_path("zsh_bad_history");

    let output = histutils(&["--output-format", "zsh", &data_file]);

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout, ": 100:1;ok\n");
}

#[test]
fn output_format_mixed_error() {
    let temp_file1 = TempFile::with_content(": 1234567891:0;echo foo\n");
    let temp_file2 = TempFile::with_content("- cmd: echo bar\n  when: 1234567892\n");

    let output = histutils(&[temp_file1.path_str(), temp_file2.path_str()]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        stderr,
        "usage: --output-format= required when multiple input formats are given\n"
    );
}

#[test]
fn detect_output_format_sh() {
    let temp_file = TempFile::with_content("echo hello\n");

    let output = histutils(&[temp_file.path_str()]);

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("failed to convert to string");
    assert_eq!(stdout, "echo hello\n");
}

#[test]
fn detect_output_format_zsh() {
    let temp_file = TempFile::with_content(": 123:0;echo hello\n");

    let output = histutils(&[temp_file.path_str()]);

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("failed to convert to string");
    assert_eq!(stdout, ": 123:0;echo hello\n");
}

#[test]
fn detect_output_format_fish() {
    let temp_file = TempFile::with_content("- cmd: echo hello\n  when: 123\n");

    let output = histutils(&[temp_file.path_str()]);

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("failed to convert to string");
    assert_eq!(stdout, "- cmd: echo hello\n  when: 123\n");
}

#[test]
fn detect_output_format_sh_multiple() {
    let temp_file1 = TempFile::with_content("echo foo\n");
    let temp_file2 = TempFile::with_content("echo bar\n");
    let temp_file3 = TempFile::with_content("echo baz\n");

    let output = histutils(&[
        temp_file1.path_str(),
        temp_file2.path_str(),
        temp_file3.path_str(),
    ]);

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("failed to convert to string");
    assert_eq!(stdout, "echo foo\necho bar\necho baz\n");
}

#[test]
fn detect_output_format_zsh_multiple() {
    let temp_file1 = TempFile::with_content(": 1:0;echo foo\n");
    let temp_file2 = TempFile::with_content(": 2:0;echo bar\n");
    let temp_file3 = TempFile::with_content(": 3:0;echo baz\n");

    let output = histutils(&[
        temp_file1.path_str(),
        temp_file2.path_str(),
        temp_file3.path_str(),
    ]);

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("failed to convert to string");
    assert_eq!(stdout, ": 1:0;echo foo\n: 2:0;echo bar\n: 3:0;echo baz\n");
}

#[test]
fn detect_output_format_fish_multiple() {
    let temp_file1 = TempFile::with_content("- cmd: echo foo\n  when: 1\n");
    let temp_file2 = TempFile::with_content("- cmd: echo bar\n  when: 2\n");
    let temp_file3 = TempFile::with_content("- cmd: echo baz\n  when: 3\n");

    let output = histutils(&[
        temp_file1.path_str(),
        temp_file2.path_str(),
        temp_file3.path_str(),
    ]);

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("failed to convert to string");
    assert_eq!(
        stdout,
        "- cmd: echo foo\n  when: 1\n- cmd: echo bar\n  when: 2\n- cmd: echo baz\n  when: 3\n"
    );
}

#[test]
fn count_empty_stdin() {
    let output = histutils_with_stdin(&["--count"], b"");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "0");
}

#[test]
fn count_empty_file() {
    let temp_file = TempFile::with_content("");

    let output = histutils(&["--count", temp_file.path_str()]);

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "0");
}

#[test]
fn preserves_duplicate_commands_sh_format() {
    let temp_file1 = TempFile::with_content("echo foo\necho foo\necho bar\n");
    let temp_file2 = TempFile::with_content("echo bar\necho baz\n");

    let output = histutils(&[
        "--output-format",
        "sh",
        temp_file1.path_str(),
        temp_file2.path_str(),
    ]);

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("failed to convert to string");
    assert_eq!(stdout, "echo foo\necho foo\necho bar\necho bar\necho baz\n");
}

mod zsh {
    use super::*;

    #[test]
    fn timestamp_sorting() {
        let temp_file1 = TempFile::with_content(": 3:0;three\n: 1:0;one\n: 2:0;two\n");
        let temp_file2 = TempFile::with_content(": 0:0;zero\n: 4:0;four\n");

        let output = histutils(&[temp_file1.path_str(), temp_file2.path_str()]);

        assert!(output.status.success());
        let stdout = String::from_utf8(output.stdout).expect("failed to convert to string");
        assert_eq!(
            stdout,
            ": 0:0;zero\n: 1:0;one\n: 2:0;two\n: 3:0;three\n: 4:0;four\n"
        );
    }

    #[test]
    fn preserves_order_same_timestamp() {
        let temp_file1 = TempFile::with_content(": 100:0;first\n: 100:0;second\n: 100:0;third\n");
        let temp_file2 = TempFile::with_content(": 100:0;fourth\n: 100:0;fifth\n");

        let output = histutils(&[temp_file1.path_str(), temp_file2.path_str()]);

        assert!(output.status.success());
        let stdout = String::from_utf8(output.stdout).expect("failed to convert to string");
        assert_eq!(
            stdout,
            ": 100:0;first\n: 100:0;second\n: 100:0;third\n: 100:0;fourth\n: 100:0;fifth\n"
        );
    }

    #[test]
    fn deduplicates_exact_matches() {
        let temp_file1 = TempFile::with_content(": 1:0;one\n: 1:0;one\n: 2:0;two\n");
        let temp_file2 = TempFile::with_content(": 1:0;one\n: 2:0;two\n: 3:0;three\n");

        let output = histutils(&[temp_file1.path_str(), temp_file2.path_str()]);

        assert!(output.status.success());
        let stdout = String::from_utf8(output.stdout).expect("failed to convert to string");
        assert_eq!(stdout, ": 1:0;one\n: 2:0;two\n: 3:0;three\n");
    }
}

mod fish {
    use super::*;

    #[test]
    fn bad_when() {
        let temp_file = TempFile::with_content("- cmd: echo\n  when: abc\n- cmd: ok\n  when: 1\n");
        let temp_path = temp_file.path_str();
        let output = histutils(&["--count", temp_path]);

        assert!(output.status.success());
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(stdout.trim(), "1");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains(format!("{temp_path}:1: parse int error").as_str()));
        assert!(stderr.contains("when: abc"));
    }

    #[test]
    fn bad_property() {
        let temp_file = TempFile::with_content("- cmd: echo\n  who: 1\n- cmd: ok\n  when: 1\n");
        let temp_path = temp_file.path_str();
        let output = histutils(&["--count", temp_path]);

        assert!(output.status.success());
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(stdout.trim(), "1");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains(format!("{temp_path}:1: bad fish header").as_str()));
        assert!(stderr.contains("who: 1"));
    }
}
