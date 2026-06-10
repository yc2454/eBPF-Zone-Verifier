import re,sys
# Usage: decode_canon.py <kernel_hash_lines_file>
#   where the file holds the chunked `bcf_canonical_hash: ... off=N bytes: ..`
#   lines for ONE hash (copied from `dmesg | grep "hash=0x<HASH>"`).
# reconstruct bytes ordered by off
chunks={}
for line in open(sys.argv[1] if len(sys.argv)>1 else '/tmp/kernel_hash_lines.txt'):
    m=re.search(r'off=(\d+) bytes:\s*([0-9a-f ]+)',line)
    if m:
        off=int(m.group(1)); hexs=m.group(2).split()
        chunks[off]=bytes(int(x,16) for x in hexs)
data=b''.join(chunks[o] for o in sorted(chunks))
print('total bytes',len(data))
OPS={0x10:'JEQ',0x50:'JNE',0x20:'JGT',0x30:'JGE',0x60:'JSGT',0x70:'JSGE',0xa0:'JLT',0xb0:'JLE',0xc0:'JSLT',0xd0:'JSLE',0x40:'JSET',
     0x00:'?00',0x04:'ADD',0x0c:'SUB',0x5c:'AND',0x4c:'OR',0x74:'RSH',0x64:'LSH',0x16:'?16'}
def opname(c):
    base=c & 0xf0 if (c&0xf0) in OPS else c & ~0x1
    return OPS.get(c & 0xf0, OPS.get(c,'0x%02x'%c))
i=0; rec=0
def u16(b,o): return b[o]|(b[o+1]<<8)
def u32(b,o): return b[o]|(b[o+1]<<8)|(b[o+2]<<16)|(b[o+3]<<24)
while i < len(data):
    tag=data[i]; 
    if tag not in (1,2,3): print('  STOP non-tag 0x%02x at %d'%(tag,i)); break
    code=data[i+1]; vlen=data[i+2]; params=u16(data,i+3); i+=5
    name={1:'VAR',2:'CONST',3:'OP'}[tag]
    extra=''
    if tag==1:
        idx=u32(data,i); i+=4; args=[u32(data,i+4*k) for k in range(vlen)]; i+=4*vlen
        extra='renamed_var=%d args=%s'%(idx,args)
    elif tag==2:
        args=[u32(data,i+4*k) for k in range(vlen)]; i+=4*vlen
        val=args[0]|(args[1]<<32) if vlen>=2 else (args[0] if args else 0)
        extra='const=%d(0x%x) args=%s'%(val,val,args)
    else:
        extra='(internal, %d children)'%vlen
    print('[%2d] %-5s code=0x%02x(%s) w=%d vlen=%d %s'%(rec,name,code,opname(code),params,vlen,extra))
    rec+=1
