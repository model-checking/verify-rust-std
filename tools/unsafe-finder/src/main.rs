use std::env;
use std::fs;
use std::error::Error;
use std::process;
use std::path::Path;

use std::collections::HashMap;

use itertools::Itertools;

use serde::Serialize;
use serde::Deserialize;

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

#[derive(Clone)]
struct StructuredFnName {
    trait_impl: Option<(String, String)>, // type as trait
    module_path: Vec<String>,
    type_parameters: Vec<String>,
    item: String,
    is_public: bool
}

fn split_by_double_colons(s:&str) -> Vec<String> {
    let mut bracket_level = 0;
    let mut current_string = String::new();
    let mut previous_strings = vec![];
    let mut colons = 0;
    for c in s.chars() {
	current_string.push(c);
	match c {
	    '<' => bracket_level += 1,
	    '>' => bracket_level -= 1,
	    ':' => {
		if bracket_level > 0 { continue; }
		colons += 1;
		if colons == 2 {
		    colons = 0;
		    previous_strings.push(current_string[..current_string.len()-2].to_string());
		    current_string.clear();
		}},
	    _ => ()
	}
    }
    previous_strings.push(current_string.clone());
    previous_strings
}

fn split_by_commas(s:&str) -> Vec<String> {
    let mut bracket_level = 0;
    let mut parens_level = 0;
    let mut current_string = String::new();
    let mut previous_strings = vec![];
    for c in s.chars() {
	current_string.push(c);
	match c {
	    '<' => bracket_level += 1,
	    '>' => bracket_level -= 1,
	    '(' => parens_level += 1,
	    ')' => parens_level -= 1,
	    ',' => {
		if bracket_level > 0 || parens_level > 0 { continue; }
		previous_strings.push(current_string[..current_string.len()-1].trim().to_string());
		current_string.clear();
	    },
	    _ => ()
	}
    }
    previous_strings.push(current_string.trim().to_string().clone());
    previous_strings
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
	assert_eq!(result, ["a","b"]);
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
}

fn parse_fn_name(raw_name:String, is_public:bool) -> StructuredFnName {
    let trait_impl_re = Regex::new(r"<(.+) as (.+)>").unwrap();
    let brackets_re = Regex::new(r"<(.+)>").unwrap();
    
    let parts:Vec<String> = split_by_double_colons(&raw_name).into_iter().rev().collect();

    if parts.len() == 2 && trait_impl_re.is_match(&parts[1]) {
        let ti_captures = trait_impl_re.captures(&parts[1]).unwrap();
        return StructuredFnName {
            trait_impl: Some((ti_captures[1].to_string(), ti_captures[2].to_string())),
            module_path: vec![],
            type_parameters: vec![],
            item: parts[0].to_string(),
            is_public: is_public
        }
    }

    let mut parts_index = 0;
    let item = &parts[parts_index]; parts_index += 1;
    let tp = &parts[parts_index].as_str();
    let type_parameters = if brackets_re.is_match(tp) {
        let tp_commas = &brackets_re.captures(tp).unwrap();
	parts_index += 1;
        split_by_commas(&tp_commas[1]).into_iter().map(|x| x.to_string()).collect()
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
        is_public: is_public
    }
}

fn handle_file(path:&Path) -> Result<(), Box<dyn Error>> {
    let path_contents = fs::read_to_string(&path).expect("unable to read file");
    let mut rdr = csv::ReaderBuilder::new().delimiter(b';').from_reader(path_contents.as_bytes());

    println!("# Unsafe usages in file {}", path.display());

    let mut fns_by_modules: HashMap<Vec<String>, Vec<StructuredFnName>> = HashMap::new();
    
    for result in rdr.deserialize() {
        let fn_stats: FnStats = result?;
	if matches!(fn_stats.is_unsafe, Some(true)) || matches!(fn_stats.has_unsafe_ops, Some(true)) {
	    let structured_fn_name = parse_fn_name(fn_stats.name, fn_stats.is_public.is_some() && fn_stats.is_public.unwrap());
	    match fns_by_modules.get_mut(&structured_fn_name.module_path) {
		Some(fns) => fns.push(structured_fn_name.clone()),
		None => { fns_by_modules.insert(structured_fn_name.module_path.clone(), vec![structured_fn_name.clone()]); }
	    }
	}
    }

    for mp in fns_by_modules.keys().sorted() {
	println!("modules {:?}", mp);
	if let Some(fns) = fns_by_modules.get(mp) {
	    for structured_fn_name in fns {
		println!("--- unsafe-containing fn {} {}", structured_fn_name.item, if structured_fn_name.is_public { "[pub]" } else { "" } );
                if let Some(ti) = &structured_fn_name.trait_impl {
                    println!("    trait impl: type {} as trait {}", ti.0, ti.1);
                } else {}
		if !structured_fn_name.type_parameters.is_empty() {
		    println!("    type parameters {:?}", structured_fn_name.type_parameters);
		}
	    }
	}
    }
    
    Ok(())
}

fn main() {
    let mut args = env::args();
    let _ = args.next(); // executable name

    if args.len() == 0 {
	// should we only handle files named "_scan_functions.csv"?
        eprintln!("Usage: unsafe-finder [[prefix]_scan_functions.csv]*");
        process::exit(1);
    }

    for arg in args {
        let path = Path::new(&arg);
        if let Err(err) = handle_file(&path) {
	    eprintln!("error processing {}: {}", arg, err);
	    process::exit(1);
	}
    }
}
