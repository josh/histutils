use std::io::Write;
use std::process::{Command, Stdio};

#[test]
fn prints_help() {
    let bin = env!("CARGO_BIN_EXE_histutils");
    let output = Command::new(bin)
        .arg("--help")
        .output()
        .expect("failed to run process");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("usage: histutils"));
}

#[test]
fn counts_entries_from_stdin() {
    let bin = env!("CARGO_BIN_EXE_histutils");
    let mut child = Command::new(bin)
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
    let bin = env!("CARGO_BIN_EXE_histutils");
    let output = Command::new(bin)
        .arg("--format")
        .arg("wat")
        .output()
        .expect("failed to run process");

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("unknown format: wat"));
}
