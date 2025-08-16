use histutils::ShellFormat;
use std::env;
use std::fs::File;
use std::io;

fn main() -> io::Result<()> {
    let mut args = env::args().skip(1);

    let entries = if let Some(path) = args.next() {
        let f = File::open(path)?;
        histutils::parse_reader(f)?
    } else {
        histutils::parse_reader(io::stdin())?
    };

    let mut stdout = io::stdout();
    histutils::write_entries(&mut stdout, entries, ShellFormat::ZshExtended)?;

    Ok(())
}
