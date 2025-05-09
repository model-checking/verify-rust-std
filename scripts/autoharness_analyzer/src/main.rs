use anyhow::Result;
use clap::Parser;
use make_tables::compute_metrics;
use parse_scanner_output::process_scan_fns;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::{
    collections::{BTreeMap, HashMap},
    fs,
    path::Path,
};
use strum_macros::{Display, EnumString};

mod make_tables;
mod parse_scanner_output;

#[derive(Parser, Debug)]
struct Args {
    /// Path to directory with kani_metadata.json files
    #[arg(required = true)]
    metadata_dir_path: String,

    /// Scanner results directory path
    #[arg(required = true)]
    scanner_results_path: String,

    /// Generate per-crate tables instead of combined data
    #[arg(long)]
    per_crate: bool,

    /// Process only the specified crate
    #[arg(long, value_name = "CRATE")]
    for_crate: Option<String>,

    /// Show precise types in the output tables
    #[arg(long)]
    show_precise_types: bool,

    /// Only output data for unsafe functions
    #[arg(long)]
    unsafe_fns_only: bool,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AutoHarnessMetadata {
    /// Functions we generated automatic harnesses for.
    pub chosen: Vec<String>,
    /// Map function names to the reason why we did not generate an automatic harness for that function.
    /// We use an ordered map so that when we print the data, it is ordered alphabetically by function name.
    pub skipped: BTreeMap<String, AutoHarnessSkipReason>,
}

/// Reasons that Kani does not generate an automatic harness for a function.
#[derive(Debug, Clone, Serialize, Deserialize, Display, EnumString)]
pub enum AutoHarnessSkipReason {
    /// The function is generic.
    #[strum(serialize = "Generic Function")]
    GenericFn,
    /// A Kani-internal function: already a harness, implementation of a Kani associated item or Kani contract instrumentation functions).
    #[strum(serialize = "Kani implementation")]
    KaniImpl,
    /// At least one of the function's arguments does not implement kani::Arbitrary
    /// (The Vec<(String, String)> contains the list of (name, type) tuples for each argument that does not implement it
    #[strum(serialize = "Missing Arbitrary implementation for argument(s)")]
    MissingArbitraryImpl(Vec<(String, String)>),
    /// The function does not have a body.
    #[strum(serialize = "The function does not have a body")]
    NoBody,
    /// The function doesn't match the user's provided filters.
    #[strum(serialize = "Did not match provided filters")]
    UserFilter,
}

impl Default for AutoHarnessMetadata {
    fn default() -> Self {
        Self::new()
    }
}

impl AutoHarnessMetadata {
    pub fn new() -> Self {
        Self {
            chosen: Vec::new(),
            skipped: BTreeMap::new(),
        }
    }

    pub fn extend(&mut self, other: AutoHarnessMetadata) {
        self.chosen.extend(other.chosen);
        self.skipped.extend(other.skipped);
    }
}

fn main() -> Result<()> {
    let args = Args::parse();

    // Collection of data from all crates
    let mut cross_crate_fn_to_row_data = HashMap::new();
    let mut cross_crate_autoharness_md = AutoHarnessMetadata::new();

    // Iterate over all kani-metadata.json files; one per crate
    for entry in fs::read_dir(&args.metadata_dir_path)? {
        let entry = entry?;
        let path = entry.path();
        if !path.to_string_lossy().contains("kani-metadata.json") {
            continue;
        }

        let kani_md_file_data =
            std::fs::read_to_string(&path).unwrap_or_else(|_| panic!("Unable to read {:?}", path));
        let v: Value = serde_json::from_str(&kani_md_file_data)?;
        let crate_name = v["crate_name"].as_str().unwrap();

        // Skip if a specific crate was requested and this isn't it
        if let Some(ref target_crate) = args.for_crate {
            if target_crate != crate_name {
                continue;
            }
        }

        println!("Processing crate {crate_name}");

        let scanner_fn_csv = format!(
            "{}/{}_scan_functions.csv",
            args.scanner_results_path, crate_name
        );
        let scanner_fn_csv_path = Path::new(&scanner_fn_csv);
        let fn_to_row_data = process_scan_fns(scanner_fn_csv_path)?;

        let autoharness_md: AutoHarnessMetadata =
            serde_json::from_value(v["autoharness_md"].clone())?;

        if args.per_crate {
            // Process each crate separately
            compute_metrics(
                crate_name,
                &autoharness_md,
                &fn_to_row_data,
                args.show_precise_types,
                args.unsafe_fns_only,
            )?;
        } else if args.for_crate.is_some() {
            return compute_metrics(
                crate_name,
                &autoharness_md,
                &fn_to_row_data,
                args.show_precise_types,
                args.unsafe_fns_only,
            );
        } else {
            cross_crate_fn_to_row_data.extend(fn_to_row_data);
            cross_crate_autoharness_md.extend(autoharness_md);
        }
    }

    // Process combined data if not doing per-crate or single-crate analysis
    if !args.per_crate {
        compute_metrics(
            "all_crates",
            &cross_crate_autoharness_md,
            &cross_crate_fn_to_row_data,
            args.show_precise_types,
            args.unsafe_fns_only,
        )?;
    }

    Ok(())
}
