# Agents Guide

This project is written in Rust and assumes Rust 1.89 or newer.

## Environment Setup

1. Install Rust 1.89 or later via rustup

## Dependencies

This project uses only the Rust standard library.

- No external crates: do not add new dependencies to `Cargo.toml`.
- Write all code using `std` only (including tests and examples).

## Testing

Run tests with:

```sh
$ cargo test
```

### Testing

Only write integration tests in `tests/cli_test.rs` that test via CLI binary invocation. Never import `lib.rs` or write unit tests.

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

### Performance

Prefer borrowing and views over owning allocations. Expose cheap accessors like `as_str()` and format directly to writers instead of building intermediate strings. Parse with slice-based methods and only convert at boundaries; avoid allocating unless it materially improves clarity or is required for user-facing messages. Prefer concrete types and enums over `Box<dyn Trait>` and dynamic dispatch.

## Building

Build the project with:

```sh
$ cargo build
```

## Comments

Keep comments concise. Only add them when they clarify non-obvious logic.
