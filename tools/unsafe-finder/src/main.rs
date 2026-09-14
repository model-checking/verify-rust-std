use std::env;
use std::error::Error;
use std::fs;
use std::path::Path;
use std::process;

use std::collections::HashMap;
use std::sync::LazyLock;

use itertools::Itertools;

use serde::Deserialize;
use serde::Serialize;

use regex::Regex;

// from kani repo's tools/scanner/src/analysis.rs:
#[derive(Clone, Debug, Serialize, Deserialize)]
struct FnStats {
    name: String,
    is_unsafe: Option<bool>,
    has_unsafe_ops: Option<bool>,
    has_unsupported_input: Option<bool>, // i.e. a function contains coroutines, floats, fn defs, fn ptrs, interior mut, raw pointers, recursive types, and mut refs
    has_loop_or_iterator: Option<bool>,
    is_public: Option<bool>,
}

#[derive(Clone, Debug, PartialEq)]
struct StructuredFnName {
    trait_impl: Option<(String, String)>, // type as trait
    module_path: Vec<String>,
    type_parameters: Vec<String>,
    item: String,
    is_public: bool,
    typ: String,
}

fn split_by_double_colons(s: &str) -> Vec<String> {
    let mut bracket_level = 0;
    let mut prev_was_minus = false;
    let mut current_string = String::new();
    let mut previous_strings = vec![];
    let mut colons = 0;
    for c in s.chars() {
        current_string.push(c);
        match c {
            '<' => bracket_level += 1,
            '>' => {
                if !prev_was_minus {
                    bracket_level -= 1;
                }
            }
            ':' => {
                if bracket_level > 0 {
                    continue;
                }
                colons += 1;
                if colons == 2 {
                    colons = 0;
                    previous_strings.push(current_string[..current_string.len() - 2].to_string());
                    current_string.clear();
                }
            }
            _ => (),
        }
        prev_was_minus = false;
        if c == '-' {
            prev_was_minus = true
        }
    }
    previous_strings.push(current_string.clone());
    previous_strings
}

fn split_by_commas(s: &str) -> Vec<String> {
    let mut bracket_level = 0;
    let mut parens_level = 0;
    let mut prev_was_minus = false;
    let mut current_string = String::new();
    let mut previous_strings = vec![];
    for c in s.chars() {
        current_string.push(c);
        match c {
            '<' => bracket_level += 1,
            '>' => {
                if !prev_was_minus {
                    bracket_level -= 1;
                }
            }
            '(' => parens_level += 1,
            ')' => parens_level -= 1,
            ',' => {
                if bracket_level > 0 || parens_level > 0 {
                    continue;
                }
                previous_strings.push(
                    current_string[..current_string.len() - 1]
                        .trim()
                        .to_string(),
                );
                current_string.clear();
            }
            _ => (),
        }
        prev_was_minus = false;
        if c == '-' {
            prev_was_minus = true
        }
    }
    previous_strings.push(current_string.trim().to_string().clone());
    previous_strings
}

static TRAIT_IMPL: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"<(.+) as (.+)>").expect("invalid regex"));
static BRACKETS: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"<(.+)>").expect("invalid regex"));

fn parse_fn_name(raw_name: String, is_public: bool, is_unsafe: bool) -> StructuredFnName {
    let typ = if is_unsafe {
        "unsafe".to_string()
    } else {
        "unsafe-containing".to_string()
    };

    let parts: Vec<String> = split_by_double_colons(&raw_name)
        .into_iter()
        .rev()
        .collect();

    if parts.len() == 1 {
        return StructuredFnName {
            trait_impl: None,
            module_path: Vec::new(),
            type_parameters: Vec::new(),
            item: raw_name,
            is_public,
            typ,
        };
    }

    if parts.len() == 2 && TRAIT_IMPL.is_match(&parts[1]) {
        let ti_captures = TRAIT_IMPL.captures(&parts[1]).unwrap();
        return StructuredFnName {
            trait_impl: Some((ti_captures[1].to_string(), ti_captures[2].to_string())),
            module_path: vec![],
            type_parameters: vec![],
            item: parts[0].to_string(),
            is_public,
            typ,
        };
    }

    let mut parts_index = 0;
    let item = &parts[parts_index];
    parts_index += 1;
    let tp = &parts[parts_index].as_str();
    let type_parameters = if BRACKETS.is_match(tp) {
        let tp_commas = &BRACKETS.captures(tp).unwrap();
        parts_index += 1;
        split_by_commas(&tp_commas[1])
            .into_iter()
            .map(|x| x.to_string())
            .filter(|x| !x.starts_with("impl"))
            .collect()
    } else {
        vec![]
    };
    let mut mp = vec![];
    while parts_index < parts.len() {
        mp.push(parts[parts_index].to_string());
        parts_index += 1;
    }

    StructuredFnName {
        trait_impl: None,
        module_path: mp.into_iter().rev().collect(),
        type_parameters: type_parameters.into_iter().map(|x| x.to_string()).collect(),
        item: item.to_string(),
        is_public,
        typ,
    }
}

fn handle_file(path: &Path) -> Result<(), Box<dyn Error>> {
    let path_contents = fs::read_to_string(path)?;
    let mut rdr = csv::ReaderBuilder::new()
        .delimiter(b';')
        .from_reader(path_contents.as_bytes());

    println!("# Unsafe usages in file {}", path.display());

    let mut fns_by_modules: HashMap<Vec<String>, Vec<StructuredFnName>> = HashMap::new();

    for result in rdr.deserialize() {
        let fn_stats: FnStats = result?;
        let is_unsafe = matches!(fn_stats.is_unsafe, Some(true));
        let is_public = matches!(fn_stats.is_public, Some(true));
        let structured_fn_name = parse_fn_name(fn_stats.name, is_public, is_unsafe);
        if is_unsafe || (!is_unsafe && matches!(fn_stats.has_unsafe_ops, Some(true))) {
            match fns_by_modules.get_mut(&structured_fn_name.module_path) {
                Some(fns) => fns.push(structured_fn_name.clone()),
                None => {
                    fns_by_modules.insert(
                        structured_fn_name.module_path.clone(),
                        vec![structured_fn_name.clone()],
                    );
                }
            }
        }
    }

    for mp in fns_by_modules.keys().sorted() {
        println!(
            "modules {:?} {}",
            mp,
            if mp.is_empty() {
                "(including trait impls)"
            } else {
                ""
            }
        );
        if let Some(fns) = fns_by_modules.get(mp) {
            for structured_fn_name in fns {
                println!(
                    "--- {} fn {} {}",
                    structured_fn_name.typ,
                    structured_fn_name.item,
                    if structured_fn_name.is_public {
                        "[pub]"
                    } else {
                        ""
                    }
                );
                if let Some(ti) = &structured_fn_name.trait_impl {
                    println!("    trait impl: type {} as trait {}", ti.0, ti.1);
                }
                if !structured_fn_name.type_parameters.is_empty() {
                    println!(
                        "    type parameters {:?}",
                        structured_fn_name.type_parameters
                    );
                }
            }
        }
    }

    Ok(())
}

fn main() {
    let mut args = env::args();
    let _ = args.next(); // skip executable name

    if args.len() == 0 {
        eprintln!("Usage: unsafe-finder [[prefix]_scan_functions.csv]*");
        process::exit(1);
    }

    for arg in args {
        if !arg.ends_with("_scan_functions.csv") {
            eprintln!(
                "error: filename {} does not end with _scan_functions.csv",
                arg
            );
            process::exit(1);
        }
        let path = Path::new(&arg);
        if let Err(err) = handle_file(path) {
            eprintln!("error processing {}: {}", arg, err);
            process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn colons_singleton() {
        let result = split_by_double_colons("a");
        assert_eq!(result, ["a"]);
    }

    #[test]
    fn colons_no_brackets() {
        let result = split_by_double_colons("one::two");
        assert_eq!(result, ["one", "two"]);
    }

    #[test]
    fn colons_brackets_no_colons() {
        let result = split_by_double_colons("one::<two>::three");
        assert_eq!(result, ["one", "<two>", "three"]);
    }

    #[test]
    fn colons_brackets_with_colons() {
        let result = split_by_double_colons("one::<two::four>::three");
        assert_eq!(result, ["one", "<two::four>", "three"]);
    }

    #[test]
    fn colons_arrow() {
        let result = split_by_double_colons("mymod::<fn()->bar::Baz>::the_item");
        assert_eq!(result, ["mymod", "<fn()->bar::Baz>", "the_item"]);
    }

    #[test]
    fn commas_singleton() {
        let result = split_by_commas("a");
        assert_eq!(result, ["a"]);
    }

    #[test]
    fn commas_brackets() {
        let result = split_by_commas("<a,b>");
        assert_eq!(result, ["<a,b>"]);
    }

    #[test]
    fn commas_no_brackets() {
        let result = split_by_commas("a, b");
        assert_eq!(result, ["a", "b"]);
    }

    #[test]
    fn commas_parens() {
        let result = split_by_commas("(a,b)");
        assert_eq!(result, ["(a,b)"]);
    }

    #[test]
    fn commas_unmatched() {
        let result = split_by_commas("<a,b),c");
        assert_eq!(result, ["<a,b),c"]);
    }

    #[test]
    fn commas_arrow() {
        let result = split_by_commas("mymod, <fn()->bar::Baz>, the_item");
        assert_eq!(result, ["mymod", "<fn()->bar::Baz>", "the_item"]);
    }

    #[test]
    fn parse_fn_name_insufficient_segments() {
        let result = parse_fn_name("foo".to_string(), false, false);
        assert_eq!(
            result,
            StructuredFnName {
                trait_impl: None,
                module_path: Vec::new(),
                type_parameters: Vec::new(),
                item: "foo".to_string(),
                is_public: false,
                typ: "unsafe-containing".to_string()
            }
        );
    }

    #[test]
    fn parse_fn_name_trait_impl() {
        let result = parse_fn_name(
            "<std::fs::Permissions as std::os::unix::fs::PermissionsExt>::from_mode".to_string(),
            false,
            false,
        );
        assert_eq!(
            result,
            StructuredFnName {
                trait_impl: Some((
                    "std::fs::Permissions".to_string(),
                    "std::os::unix::fs::PermissionsExt".to_string()
                )),
                module_path: Vec::new(),
                type_parameters: Vec::new(),
                item: "from_mode".to_string(),
                is_public: false,
                typ: "unsafe-containing".to_string()
            }
        );
    }

    #[test]
    fn parse_fn_name_with_generics() {
        let result = parse_fn_name(
            "std::sync::mpmc::list::Channel::<T>::len".to_string(),
            false,
            false,
        );
        assert_eq!(
            result,
            StructuredFnName {
                trait_impl: None,
                module_path: [
                    "std".to_string(),
                    "sync".to_string(),
                    "mpmc".to_string(),
                    "list".to_string(),
                    "Channel".to_string()
                ]
                .to_vec(),
                type_parameters: ["T".to_string()].to_vec(),
                item: "len".to_string(),
                is_public: false,
                typ: "unsafe-containing".to_string()
            }
        );
    }
}
