use std::fs::File;

mod gamma0 {
    include!(concat!(env!("OUT_DIR"), "/gamma0.rs"));
}

#[test]
fn gamma_0() {
    let parser = gamma0::parse("aac");
    parser
        .gss
        .print(&mut File::create(concat!(env!("CARGO_MANIFEST_DIR"), "/../target/gamma0-gss.dot")).unwrap())
        .unwrap();
    parser
        .sppf
        .print(&mut File::create(concat!(env!("CARGO_MANIFEST_DIR"), "/../target/gamma0-sppf.dot")).unwrap())
        .unwrap();
}
