pub struct RawBpfInsn {
    pub code: u8,
    pub dst: u8,
    pub src: u8,
    pub off: i16,
    pub imm: i32,
}

pub fn decode_insns(bytes: &[u8]) -> Vec<RawBpfInsn> {
    let mut insns = Vec::new();
    let mut i = 0;
    while i + 8 <= bytes.len() {
        let code = bytes[i];
        let reg = bytes[i + 1];
        let dst = reg & 0x0F;
        let src = reg >> 4;
        let off = i16::from_le_bytes([bytes[i + 2], bytes[i + 3]]);
        let imm = i32::from_le_bytes([bytes[i + 4], bytes[i + 5], bytes[i + 6], bytes[i + 7]]);
        insns.push(RawBpfInsn { code, dst, src, off, imm });
        i += 8;
    }
    insns
}
