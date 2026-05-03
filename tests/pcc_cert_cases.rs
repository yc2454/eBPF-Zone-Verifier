use std::path::PathBuf;
use std::process::Command;

#[test]
fn pcc_certificate_cases_are_reproducible() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cert_cases = manifest_dir.join("pcc-tests").join("cert_cases.json");

    let output = Command::new(env!("CARGO_BIN_EXE_zovia"))
        .arg("pcc-regress")
        .arg(&cert_cases)
        .current_dir(&manifest_dir)
        .output()
        .expect("failed to run zovia pcc-regress");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "pcc-regress exited with {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr
    );
    assert!(
        stdout.contains("PCC certificate case summary:") && stdout.contains("0 failed"),
        "unexpected summary in stdout:\n{}",
        stdout
    );
}
