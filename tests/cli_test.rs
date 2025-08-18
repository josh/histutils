use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

fn get_bin() -> &'static str {
    env!("CARGO_BIN_EXE_histutils")
}

fn histutils(args: &[&str]) -> std::process::Output {
    Command::new(get_bin())
        .args(args)
        .output()
        .expect("failed to run process")
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
    assert!(stdout.contains("usage: histutils"));
}

#[test]
fn prints_version() {
    let output = histutils(&["--version"]);

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);

    let expected_version = env!("CARGO_PKG_VERSION");
    assert!(
        stdout.contains(expected_version),
        "Expected version {expected_version}, got: {stdout}"
    );
}

#[test]
fn bad_format() {
    let output = histutils(&["--format", "foo"]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("unknown format: foo"));
}

#[test]
fn count_stdin() {
    let mut child = Command::new(get_bin())
        .arg("--count")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed to spawn process");

    {
        let stdin = child.stdin.as_mut().expect("failed to open stdin");
        stdin
            .write_all(b"foo\nbar\nbaz\n")
            .expect("failed to write to stdin");
    }

    let output = child.wait_with_output().expect("failed to wait on child");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "3");
}

#[test]
fn count_zsh_history() {
    let data_file = test_data_path("zsh_common_history");

    let output = histutils(&["--count", &data_file]);

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "8");
}

#[test]
fn reads_fish_history() {
    let data_file = test_data_path("fish_common_history");

    let output = histutils(&["--count", &data_file]);

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "8");
}

#[test]
fn reads_sh_history() {
    let data_file = test_data_path("sh_history");

    let output = histutils(&["--count", &data_file]);

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "8");
}

#[test]
fn roundtrip_sh_history() {
    let data_file = test_data_path("sh_history");
    let input_str = std::fs::read_to_string(&data_file).expect("failed to read file");

    let output = histutils(&["--format", "sh", &data_file]);
    let output_str = String::from_utf8(output.stdout).expect("failed to convert to string");

    assert!(output.status.success());
    assert_eq!(output_str, input_str);
}

#[test]
fn roundtrip_zsh_common_history() {
    let data_file = test_data_path("zsh_common_history");
    let input_str = std::fs::read_to_string(&data_file).expect("failed to read file");

    let output = histutils(&["--format", "zsh", &data_file]);
    let output_str = String::from_utf8(output.stdout).expect("failed to convert to string");

    assert!(output.status.success());
    assert_eq!(output_str, input_str);
}

#[test]
fn roundtrip_zsh_duration_history() {
    let data_file = test_data_path("zsh_duration_history");
    let input_str = std::fs::read_to_string(&data_file).expect("failed to read file");

    let output = histutils(&["--format", "zsh", &data_file]);
    let output_str = String::from_utf8(output.stdout).expect("failed to convert to string");

    assert!(output.status.success());
    assert_eq!(output_str, input_str);
}

#[test]
fn roundtrip_fish_common_history() {
    let data_file = test_data_path("fish_common_history");
    let input_str = std::fs::read_to_string(&data_file).expect("failed to read file");

    let output = histutils(&["--format", "fish", &data_file]);
    let output_str = String::from_utf8(output.stdout).expect("failed to convert to string");

    assert!(output.status.success());
    assert_eq!(output_str, input_str);
}

#[test]
fn roundtrip_fish_paths_history() {
    let data_file = test_data_path("fish_paths_history");
    let input_str = std::fs::read_to_string(&data_file).expect("failed to read file");

    let output = histutils(&["--format", "fish", &data_file]);
    let output_str = String::from_utf8(output.stdout).expect("failed to convert to string");

    assert!(output.status.success());
    assert_eq!(output_str, input_str);
}

#[test]
fn lossless_zsh_to_fish() {
    let input_data_file = test_data_path("zsh_common_history");
    let output_data_file = test_data_path("fish_common_history");

    let output = histutils(&["--format", "fish", &input_data_file]);
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

    let output = histutils(&["--format", "zsh", &input_data_file]);
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

    let output = histutils(&["--format", "sh", &input_data_file]);
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

    let output = histutils(&["--format", "sh", &input_data_file]);
    let actual_output_str = String::from_utf8(output.stdout).expect("failed to convert to string");
    let expected_output_str =
        std::fs::read_to_string(&output_data_file).expect("failed to read file");

    assert!(output.status.success());
    assert_eq!(actual_output_str, expected_output_str);
}

#[test]
fn sh_to_zsh_missing_epoch() {
    let input_data_file = test_data_path("sh_history");

    let output = histutils(&["--format", "zsh", &input_data_file]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("usage: --epoch="));
    assert!(stderr.contains("zsh"));
}
