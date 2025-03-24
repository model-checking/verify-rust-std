use mdbook::book::{Book, Chapter};
use mdbook::errors::Error;
use mdbook::preprocess::{CmdPreprocessor, Preprocessor, PreprocessorContext};
use mdbook::BookItem;
use std::{env, io, path::Path, process::Command};

fn main() {
    let mut args = std::env::args().skip(1);
    match args.next().as_deref() {
        Some("supports") => {
            // Supports all renderers.
            return;
        }
        Some(arg) => {
            eprintln!("unknown argument: {arg}");
            std::process::exit(1);
        }
        None => {}
    }

    if let Err(e) = handle_preprocessing() {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}

// Plot the Kani metrics.
// The mdbook builder reads the postprocessed book from stdout,
// so suppress all Command output to avoid having its output interpreted as part of the book
fn run_kani_metrics_script() -> Result<(), Error> {
    // This will be the absolute path to the "doc/" folder
    let original_dir = env::current_dir()?;
    let tools_path = original_dir.join(Path::new("doc/src/tools"));

    let kani_std_analysis_path = Path::new("scripts/kani-std-analysis");
    env::set_current_dir(kani_std_analysis_path)?;

    Command::new("pip")
        .args(&["install", "-r", "requirements.txt"])
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()?;

    Command::new("python")
        .args(&[
            "kani_std_analysis.py",
            "--crate",
            "core",
            "--metrics-file",
            "metrics-data-core.json",
            "--plot-only",
            "--plot-dir",
            &tools_path.to_string_lossy(),
        ])
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()?;

    Command::new("python")
        .args(&[
            "kani_std_analysis.py",
            "--crate",
            "std",
            "--metrics-file",
            "metrics-data-std.json",
            "--plot-only",
            "--plot-dir",
            &tools_path.to_string_lossy(),
        ])
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()?;

    env::set_current_dir(&original_dir)?;

    Ok(())
}

struct AddKaniGraphs;

impl Preprocessor for AddKaniGraphs {
    fn name(&self) -> &str {
        "add-metrics"
    }

    fn run(&self, _ctx: &PreprocessorContext, mut book: Book) -> Result<Book, Error> {
        book.for_each_mut(|item| {
            if let BookItem::Chapter(ch) = item {
                if ch.name == "Kani" {
                    add_graphs(ch);
                    return;
                }
            }
        });
        Ok(book)
    }
}

fn add_graphs(chapter: &mut Chapter) {
    let new_content = r#"
## Kani Metrics

Note that these metrics are for x86-64 architectures.

### `core`
![Unsafe Metrics](core_unsafe_metrics.png)

![Safe Abstractions Metrics](core_safe_abstractions_metrics.png)

![Safe Metrics](core_safe_metrics.png)

### `std`
![Unsafe Metrics](std_unsafe_metrics.png)

![Safe Abstractions Metrics](std_safe_abstractions_metrics.png)

![Safe Metrics](std_safe_metrics.png)
"#;

    chapter.content.push_str(new_content);
}

pub fn handle_preprocessing() -> Result<(), Error> {
    run_kani_metrics_script()?;
    let pre = AddKaniGraphs;
    let (ctx, book) = CmdPreprocessor::parse_input(io::stdin())?;

    let processed_book = pre.run(&ctx, book)?;
    serde_json::to_writer(io::stdout(), &processed_book)?;

    Ok(())
}
