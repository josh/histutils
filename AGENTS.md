# Agents Guide

This project is written in Rust and assumes Rust 1.89 or newer.

## Environment Setup

1. Install Rust 1.89 or later via rustup

## Testing

Run tests with:

```sh
$ cargo test
```

## Formatting

Format code with:

```sh
$ cargo fmt --all
```

## Code Quality

Run clippy (including pedantic lints) and treat warnings as errors:

```sh
$ cargo clippy --all-targets --all-features -- -D warnings -D clippy::pedantic
```

## Building

Build the project with:

```sh
$ cargo build
```

## Comments

Keep comments concise. Only add them when they clarify non-obvious logic.
