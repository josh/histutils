use std::io::Write;
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
    assert!(stdout.contains("histutils"));

    let expected_version = env!("CARGO_PKG_VERSION");
    assert!(
        stdout.contains(expected_version),
        "Expected version {expected_version}, got: {stdout}"
    );
}

#[test]
fn counts_entries_from_stdin() {
    let mut child = Command::new(get_bin())
        .arg("--count")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed to spawn process");

    {
        let stdin = child.stdin.as_mut().expect("failed to open stdin");
        stdin
            .write_all(b": 1:0;echo hi\n")
            .expect("failed to write to stdin");
    }

    let output = child.wait_with_output().expect("failed to wait on child");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "1");
}

#[test]
fn invalid_format_fails() {
    let output = histutils(&["--format", "wat"]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("unknown format: wat"));
}
