use super::parse::parse_btf;
use super::types::*;

/// Build a minimal BTF blob exercising DECL_TAG + kfunc registry + TYPE_TAG.
///
/// Layout:
///   id 1: FUNC     name="my_kfunc"
///   id 2: DECL_TAG name="kfunc",   target=1, component_idx=-1
///   id 3: INT      name="inner",   size=4
///   id 4: TYPE_TAG name="__kptr",  inner=3
fn synthetic_btf() -> Vec<u8> {
    // String table. Offsets matter.
    //   0  ""
    //   1  "my_kfunc\0"   (9 bytes)
    //  10  "kfunc\0"      (6 bytes)
    //  16  "__kptr\0"     (7 bytes)
    //  23  "inner\0"      (6 bytes) -> end 29
    let mut strings: Vec<u8> = Vec::new();
    strings.push(0);
    strings.extend_from_slice(b"my_kfunc\0");
    strings.extend_from_slice(b"kfunc\0");
    strings.extend_from_slice(b"__kptr\0");
    strings.extend_from_slice(b"inner\0");
    assert_eq!(strings.len(), 29);

    let mut types: Vec<u8> = Vec::new();
    let push_hdr = |out: &mut Vec<u8>, name_off: u32, info: u32, size_or_type: u32| {
        out.extend_from_slice(&name_off.to_le_bytes());
        out.extend_from_slice(&info.to_le_bytes());
        out.extend_from_slice(&size_or_type.to_le_bytes());
    };

    // Type 1: FUNC "my_kfunc"
    push_hdr(&mut types, 1, (BTF_KIND_FUNC as u32) << 24, 0);
    // Type 2: DECL_TAG "kfunc" target=1, extra i32 component_idx = -1
    push_hdr(&mut types, 10, (BTF_KIND_DECL_TAG as u32) << 24, 1);
    types.extend_from_slice(&(-1i32).to_le_bytes());
    // Type 3: INT "inner" size=4, extra 4 bytes of int encoding (zeros ok)
    push_hdr(&mut types, 23, (BTF_KIND_INT as u32) << 24, 4);
    types.extend_from_slice(&0u32.to_le_bytes());
    // Type 4: TYPE_TAG "__kptr" inner=3
    push_hdr(&mut types, 16, (BTF_KIND_TYPE_TAG as u32) << 24, 3);

    let hdr_len: u32 = 24;
    let type_len = types.len() as u32;
    let str_len = strings.len() as u32;

    let mut out = Vec::new();
    out.extend_from_slice(&0xEB9Fu16.to_le_bytes()); // magic
    out.push(1); // version
    out.push(0); // flags
    out.extend_from_slice(&hdr_len.to_le_bytes());
    out.extend_from_slice(&0u32.to_le_bytes()); // type_off
    out.extend_from_slice(&type_len.to_le_bytes());
    out.extend_from_slice(&type_len.to_le_bytes()); // str_off = after types
    out.extend_from_slice(&str_len.to_le_bytes());
    out.extend_from_slice(&types);
    out.extend_from_slice(&strings);
    out
}

#[test]
fn parse_decl_tag_populates_kfunc_registry() {
    let blob = synthetic_btf();
    let ctx = parse_btf(&blob).expect("parse");

    // kfunc registered by FUNC name
    assert_eq!(ctx.lookup_kfunc("my_kfunc"), Some(1));
    assert!(ctx.lookup_kfunc("nonexistent").is_none());

    // decl_tags_for returns the tag attached to the FUNC
    let tags: Vec<_> = ctx.decl_tags_for(1).collect();
    assert_eq!(tags.len(), 1);
    assert_eq!(tags[0].name, "kfunc");
    assert_eq!(tags[0].component_idx, -1);

    // No tags on unrelated types
    assert_eq!(ctx.decl_tags_for(3).count(), 0);
}

#[test]
fn type_tag_name_returns_tag_and_inner() {
    let ctx = parse_btf(&synthetic_btf()).expect("parse");
    let (name, inner) = ctx.type_tag_name(4).expect("type tag");
    assert_eq!(name, "__kptr");
    assert_eq!(inner, 3);
    // Non-TYPE_TAG ids return None
    assert!(ctx.type_tag_name(1).is_none());
    assert!(ctx.type_tag_name(3).is_none());
}
