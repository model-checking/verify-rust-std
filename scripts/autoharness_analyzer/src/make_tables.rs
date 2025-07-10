use anyhow::Result;

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs::File,
    io::Write,
    path::Path,
};

use to_markdown_table::MarkdownTable;

use crate::{parse_scanner_output::ScanFnsRow, AutoHarnessMetadata, AutoHarnessSkipReason};

/// Create Markdown tables with the analysis results
fn chosen_overview_table(
    autoharness_md: &AutoHarnessMetadata,
    fn_to_row_data: &HashMap<String, ScanFnsRow>,
) -> Result<MarkdownTable> {
    let mut safe_count = 0;
    let mut safe_abstractions_count = 0;
    let mut unsafe_count = 0;

    for fn_name in &autoharness_md.chosen {
        if let Some(record) = fn_to_row_data.get(fn_name) {
            if record.is_unsafe {
                unsafe_count += 1;
            } else if record.has_unsafe_ops {
                safe_abstractions_count += 1;
            } else {
                safe_count += 1;
            }
        } else {
            // See https://github.com/model-checking/verify-rust-std/pull/350#discussion_r2091698600
            // for examples of when such discrepancies appear
            println!(
                "[WARNING] Function {} is in in autoharness metadata but absent in scanner tool output",
                fn_name
            );
        }
    }

    Ok(MarkdownTable::new(
        Some(vec!["Functions with Automatic Harnesses", "Count"]),
        vec![
            vec!["Safe Functions".into(), safe_count.to_string()],
            vec![
                "Safe Abstractions".into(),
                safe_abstractions_count.to_string(),
            ],
            vec!["Unsafe Functions".into(), unsafe_count.to_string()],
            vec![
                "Total".into(),
                (safe_count + safe_abstractions_count + unsafe_count).to_string(),
            ],
        ],
    )?)
}

fn skipped_overview_table(autoharness_md: &AutoHarnessMetadata) -> Result<MarkdownTable> {
    // Map the String representation of each `AutoharnessSkipReason` to the number of times it appears
    // We convert to a string first so that we treat all MissingArbitraryImpls as the same key, instead of differentiating on its vector contents.
    let mut skip_reason_count: BTreeMap<String, u32> = BTreeMap::new();

    for reason in autoharness_md.skipped.values() {
        *skip_reason_count.entry(reason.to_string()).or_insert(0) += 1;
    }

    // Sort in decreasing order by count so that most popular categories are in the first rows
    let mut sorted_by_count = skip_reason_count.into_iter().collect::<Vec<_>>();
    sorted_by_count.sort_by(|(_, count_a), (_, count_b)| count_b.cmp(count_a));

    Ok(MarkdownTable::new(
        Some(vec![
            "Reason function was skipped".to_string(),
            "# of functions skipped for this reason".to_string(),
        ]),
        sorted_by_count
            .iter()
            .map(|(reason, count)| vec![reason.to_string(), count.to_string()])
            .chain(std::iter::once(vec![
                "Total".to_string(),
                autoharness_md.skipped.len().to_string(),
            ]))
            .collect(),
    )?)
}

fn skipped_breakdown_table(
    autoharness_md: &AutoHarnessMetadata,
    show_precise_types: bool,
) -> Result<MarkdownTable> {
    // Rust type -- &mut i32, &mut u32, bool, etc.
    type PreciseType = String;
    // Grouping of PreciseTypes into larger categories, e.g. &mut i32 and &mut u32 are both in the same category of mutable reference
    type TypeCategory = String;
    // Count occurrences of TypeCategories across function arguments
    type Count = u32;

    // The order is important; mutable references must come before immutable ones,
    // so that we check for starting with &mut before falling back on checking for just &
    let type_categories = ["&mut", "&", "*const", "*mut"].map(TypeCategory::from);
    // Map each type category to (number of occurrences, list of precise types matching the category)
    // e.g. if we encounter two &mut i32s and one &mut u32, we'd have &mut: (3, {&mut i32, &mut u32})
    let mut category_to_types: HashMap<TypeCategory, (Count, HashSet<PreciseType>)> =
        HashMap::new();

    let mut insert_category = |category: TypeCategory, arg_type: PreciseType| {
        if let Some((count, precise_types)) = category_to_types.get_mut(&category) {
            *count += 1;
            precise_types.insert(arg_type);
        } else {
            category_to_types.insert(category, (1, HashSet::from([arg_type.clone()])));
        }
    };

    for reason in autoharness_md.skipped.values() {
        if let AutoHarnessSkipReason::MissingArbitraryImpl(args) = reason {
            for (_, arg_type) in args {
                let mut is_categorized = false;
                for category in &type_categories {
                    if arg_type.starts_with(category) {
                        insert_category(category.clone(), arg_type.clone());
                        is_categorized = true;
                        // break to avoid categorizing mutable references as immutable ones as well
                        break;
                    }
                }
                if !is_categorized {
                    // If arg_type doesn't fit into one of the predefined categories,
                    // create a TypeCategory and PreciseType for it by splitting on the last double semicolon
                    // e.g. if arg_type is "num::saturating::Saturating<i16>", produce new TypeCategory "num::saturating" and PreciseType "Saturating<i16>"
                    if let Some((type_category, precise_type)) = arg_type.rsplit_once("::") {
                        insert_category(type_category.into(), precise_type.into());
                    } else {
                        insert_category("other".into(), arg_type.clone());
                    }
                }
            }
        }
    }

    // Sort in decreasing order by count so that most popular categories are in the first rows
    let mut sorted_by_count = category_to_types.into_iter().collect::<Vec<_>>();
    sorted_by_count.sort_by(|(_, (count_a, _)), (_, (count_b, _))| count_b.cmp(count_a));

    let total_precise_types = sorted_by_count
        .iter()
        .map(|(_, (_, precise_types))| precise_types.len())
        .sum::<usize>();

    Ok(MarkdownTable::new(
        Some(if show_precise_types {
            vec![
                "Unsupported Type Category".to_string(),
                "# of occurences".to_string(),
                "Precise Types".to_string(),
            ]
        } else {
            vec![
                "Unsupported Type Category".to_string(),
                "# of occurences".to_string(),
            ]
        }),
        sorted_by_count
            .into_iter()
            .map(|(category, (count, precise_types))| {
                if show_precise_types {
                    vec![
                        category.to_string(),
                        count.to_string(),
                        precise_types
                            .iter()
                            .map(|precise_type| precise_type.to_string())
                            .collect::<Vec<_>>()
                            .join(", "),
                    ]
                } else {
                    vec![category.to_string(), count.to_string()]
                }
            })
            .chain(std::iter::once(if show_precise_types {
                vec![
                    "Total".to_string(),
                    total_precise_types.to_string(),
                    "".to_string(),
                ]
            } else {
                vec!["Total".to_string(), total_precise_types.to_string()]
            }))
            .collect(),
    )?)
}

fn write_table_to_file(out_file: &mut File, table: &MarkdownTable) -> Result<()> {
    let mut table_as_string = table.to_string();
    table_as_string.push('\n');
    Ok(out_file.write_all(table_as_string.as_bytes())?)
}

pub fn compute_metrics(
    crate_name: &str,
    autoharness_md: &AutoHarnessMetadata,
    fn_to_row_data: &HashMap<String, ScanFnsRow>,
    show_precise_types: bool,
    unsafe_fns_only: bool,
) -> Result<()> {
    let unsafe_metadata = if unsafe_fns_only {
        AutoHarnessMetadata {
            chosen: autoharness_md
                .chosen
                .iter()
                .filter(|fn_name| {
                    fn_to_row_data
                        .get(*fn_name)
                        .map(|row| row.is_unsafe)
                        .unwrap_or(false)
                })
                .cloned()
                .collect(),
            skipped: autoharness_md
                .skipped
                .iter()
                .filter(|(fn_name, _)| {
                    fn_to_row_data
                        .get(*fn_name)
                        .map(|row| row.is_unsafe)
                        .unwrap_or(false)
                })
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        }
    } else {
        autoharness_md.clone()
    };

    let chosen_overview_table = chosen_overview_table(&unsafe_metadata, fn_to_row_data)?;
    let skipped_overview_table = skipped_overview_table(&unsafe_metadata)?;
    let skipped_breakdown_table = skipped_breakdown_table(&unsafe_metadata, show_precise_types)?;

    let out_path = Path::new(&format!(
        "{}{}_autoharness_data",
        crate_name,
        if unsafe_fns_only { "_unsafe" } else { "" }
    ))
    .with_extension("md");
    let mut out_file = File::create(&out_path)?;

    write_table_to_file(&mut out_file, &chosen_overview_table)?;
    write_table_to_file(&mut out_file, &skipped_overview_table)?;
    write_table_to_file(&mut out_file, &skipped_breakdown_table)?;

    println!("Wrote results to {}", out_path.to_string_lossy());

    Ok(())
}
