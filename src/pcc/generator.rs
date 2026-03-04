use crate::ast::Program;
use crate::domains::dbm::Dbm;

use std::collections::BTreeMap;

use super::model::{AnnotationEntry, PcAnnotation, ProgramCertificate, ProofStep};
use super::{generate_v1_obligations_from_zone, program_hash};

/// Generate an obligation-based certificate from zone analysis artifacts.
pub fn generate_obligation_certificate_from_zone(
    prog: &Program,
    zone_dbms: &[Dbm],
) -> ProgramCertificate {
    let mut cert = ProgramCertificate::empty(program_hash(prog));
    cert.obligations = generate_v1_obligations_from_zone(prog, zone_dbms);
    cert
}

/// Generate a prototype pc-annotation certificate from zone artifacts.
///
/// For v0.1, this derives entries from currently supported zone obligations and
/// materializes them as per-PC entries (at obligation successor PCs).
pub fn generate_pc_annotation_certificate_from_zone(
    prog: &Program,
    zone_dbms: &[Dbm],
) -> ProgramCertificate {
    let mut cert = ProgramCertificate::empty(program_hash(prog));
    let obligations = generate_v1_obligations_from_zone(prog, zone_dbms);
    let mut by_pc: BTreeMap<usize, Vec<AnnotationEntry>> = BTreeMap::new();

    for ob in obligations {
        by_pc.entry(ob.succ_pc).or_default().push(AnnotationEntry {
            i: ob.target.i,
            j: ob.target.j,
            bound: ob.target.c,
            // Single-step target proof keeps v0.1 checker simple.
            proof: vec![ProofStep::PreStateStep {
                i: ob.target.i,
                j: ob.target.j,
                c: ob.target.c,
            }],
        });
    }

    cert.pc_annotations = by_pc
        .into_iter()
        .map(|(pc, entries)| PcAnnotation { pc, entries })
        .collect();
    cert
}

/// Generate the unified prototype certificate that carries both legacy
/// obligations and pc-annotations during migration.
pub fn generate_prototype_certificate_from_zone(
    prog: &Program,
    zone_dbms: &[Dbm],
) -> ProgramCertificate {
    let mut cert = generate_obligation_certificate_from_zone(prog, zone_dbms);
    let pc_ann = generate_pc_annotation_certificate_from_zone(prog, zone_dbms);
    cert.pc_annotations = pc_ann.pc_annotations;
    cert
}
