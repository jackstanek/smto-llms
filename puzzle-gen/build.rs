//! Build script that turns the static names lists and creates const Vecs
//! containing the names.

use std::collections::HashMap;
use std::env;
use std::fs;
use std::fs::OpenOptions;
use std::io::BufWriter;
use std::io::{self, Write};
use std::path::Path;

#[derive(Debug)]
#[allow(unused)]
enum BuildError {
    IoError(io::Error),
    VarError(env::VarError),
    Custom(String),
}

impl BuildError {
    fn custom(msg: impl Into<String>) -> Self {
        BuildError::Custom(msg.into())
    }
}

impl From<io::Error> for BuildError {
    fn from(e: io::Error) -> Self {
        BuildError::IoError(e)
    }
}

impl From<env::VarError> for BuildError {
    fn from(e: env::VarError) -> Self {
        BuildError::VarError(e)
    }
}

fn main() -> Result<(), BuildError> {
    let root_dir = env::var("CARGO_MANIFEST_DIR")?;
    let names_dir = Path::new(&root_dir)
        .join("static")
        .join("data")
        .join("names");
    let mut name_map = HashMap::new();
    for filename in fs::read_dir(&names_dir)? {
        let base_path = filename?.path();
        println!("cargo:rerun-if-changed={}", base_path.display());
        let file_name = base_path
            .file_stem()
            .ok_or(BuildError::custom("unexpected file name format"))?;
        let names = name_map
            .entry(file_name.to_owned())
            .or_insert_with(Vec::new);
        for line in fs::read_to_string(&base_path)?.lines() {
            names.push(line.to_string());
        }
    }

    let out_dir = env::var("OUT_DIR")?;
    let dest_path = Path::new(&out_dir).join("names_inner.rs");
    let f = OpenOptions::new()
        .write(true)
        .create(true)
        .open(dest_path)?;
    let mut f = BufWriter::new(f);
    for (names_kind, names) in name_map {
        writeln!(
            &mut f,
            "pub static {}: &[&'static str] = &[",
            names_kind.to_string_lossy().to_uppercase()
        )?;
        for name in names {
            writeln!(&mut f, "    \"{name}\",")?;
        }
        writeln!(&mut f, "];")?;
    }

    Ok(())
}
