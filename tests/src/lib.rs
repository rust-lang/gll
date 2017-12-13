use std::fs::File;

pub mod gamma0 {
    include!(concat!(env!("OUT_DIR"), "/gamma0.rs"));
}

#[test]
fn gamma_0() {
    let mut parser = gamma0::Parser::new("aac");
    gamma0::A::parse(&mut parser);
    parser
        .gss
        .print(&mut File::create(concat!(env!("CARGO_MANIFEST_DIR"), "/../target/gamma0-gss.dot")).unwrap())
        .unwrap();
    parser
        .sppf
        .print(&mut File::create(concat!(env!("CARGO_MANIFEST_DIR"), "/../target/gamma0-sppf.dot")).unwrap())
        .unwrap();
}
