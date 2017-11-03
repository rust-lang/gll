use std::fs::File;

mod gamma0;

#[test]
fn gamma_0() {
    let parser = gamma0::parse("aac");
    parser
        .gss
        .print(&mut File::create("target/gamma0-gss.dot").unwrap())
        .unwrap();
    parser
        .sppf
        .print(&mut File::create("target/gamma0-sppf.dot").unwrap())
        .unwrap();
}
