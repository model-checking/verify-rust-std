fn main() {
    // We add the configurations here to be checked.
    println!("cargo:rustc-check-cfg=cfg(kani_host)");
}
