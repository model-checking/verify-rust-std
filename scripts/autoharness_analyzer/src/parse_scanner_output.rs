use anyhow::bail;
use anyhow::Result;
use serde::Deserialize;
use std::collections::HashMap;
use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::path::Path;

// Parse the CSV files that the Kani `scanner` tool outputs
// and store which functions are safe and unsafe

// Number of columns in {crate_name}_scan_functions.csv.
const SCANNER_COLS: usize = 6;

/// Single row of data in {crate_name}_scan_functions.csv
#[derive(Debug, Deserialize)]
#[allow(dead_code)]
pub struct ScanFnsRow {
    pub name: String,
    pub is_unsafe: bool,
    pub has_unsafe_ops: bool,
    has_unsupported_input: bool,
    has_loop_or_iterator: bool,
}

pub fn process_scan_fns(file_path: &Path) -> Result<HashMap<String, ScanFnsRow>> {
    let file = File::open(file_path).unwrap_or_else(|_| panic!("Cannot open file {:?}", file_path));
    let reader = BufReader::new(file);
    let mut fn_to_row_data = HashMap::new();

    for (index, line) in reader.lines().enumerate().skip(1) {
        let line = line?;

        // The entries are split by semicolons, but we can't just split by that since the function names can also include semicolons
        // e.g. the row "ptr::mut_ptr::<impl *mut [T; N]>::as_mut_ptr";false;false;true;false.
        // So split by ;true or ;false instead--whichever comes first--then take everything before the match as the function name
        let true_index = line.find(";true");
        let false_index = line.find(";false");

        let split_index = match (true_index, false_index) {
            (Some(t), Some(f)) => t.min(f),
            (Some(t), None) => t,
            (None, Some(f)) => f,
            (None, None) => bail!("Invalid format in line {}: {}", index + 1, line),
        };

        let (name, rest) = line.split_at(split_index);
        let mut fields = vec![name];
        // Now that we've found the function name, the rest is just booleans, so we can split by ; to get the rest
        fields.extend(rest[1..].split(';'));

        parse_row(&mut fn_to_row_data, fields, index + 1)?;
    }

    Ok(fn_to_row_data)
}

fn parse_row(
    rows: &mut HashMap<String, ScanFnsRow>,
    fields: Vec<&str>,
    line_number: usize,
) -> Result<()> {
    if fields.len() != SCANNER_COLS {
        bail!(
            "Expected {} fields, got {} in line {}. Fields: {:?}",
            SCANNER_COLS,
            fields.len(),
            line_number,
            fields
        );
    }

    let fn_name = fields[0].to_string();
    rows.insert(
        fn_name.clone(),
        ScanFnsRow {
            name: fn_name,
            is_unsafe: fields[1].parse().unwrap_or(false),
            has_unsafe_ops: fields[2].parse().unwrap_or(false),
            has_unsupported_input: fields[3].parse().unwrap_or(false),
            has_loop_or_iterator: fields[4].parse().unwrap_or(false),
        },
    );

    Ok(())
}
