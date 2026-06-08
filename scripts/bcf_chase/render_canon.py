import re,sys
def load(fn):
    chunks={}
    for line in open(fn):
        m=re.search(r'off=(\d+) bytes:\s*([0-9a-f ]+)',line)
        if m:
            chunks[int(m.group(1))]=bytes(int(x,16) for x in m.group(2).split())
    return b''.join(chunks[o] for o in sorted(chunks))
def u16(b,o): return b[o]|(b[o+1]<<8)
def u32(b,o): return b[o]|(b[o+1]<<8)|(b[o+2]<<16)|(b[o+3]<<24)
# op names by full code (low bit = BV flag, strip for name)
OPS={0x10:'==',0x50:'!=',0x20:'u>',0x30:'u>=',0x60:'s>',0x70:'s>=',0xa0:'u<',0xb0:'u<=',
     0xc0:'s<',0xd0:'s<=',0x40:'&jset',0x00:'+',0x0c:'-',0x5c:'&',0x4c:'|',0x74:'>>',0x64:'<<',0x01:'AND'}
def opn(c):
    return OPS.get(c & 0xfe, OPS.get(c,'op0x%02x'%c))
def parse(data):
    i=0; st=[]
    while i<len(data):
        tag=data[i]; code=data[i+1]; vlen=data[i+2]; w=u16(data,i+3); i+=5
        if tag==1:
            idx=u32(data,i); i+=4+4*vlen
            st.append(('v%d'%idx, w))
        elif tag==2:
            args=[u32(data,i+4*k) for k in range(vlen)]; i+=4*vlen
            val=args[0]|(args[1]<<32) if vlen>=2 else (args[0] if args else 0)
            st.append((hex(val), w))
        else:
            kids=[st.pop() for _ in range(vlen)][::-1]
            op=opn(code)
            if vlen>2:
                st.append(('AND', kids))
            else:
                st.append(('(%s %s %s)'%(render(kids[0]),op,render(kids[1]) if len(kids)>1 else ''), w))
    return st[-1]
def render(node):
    if isinstance(node,tuple) and len(node)==2 and isinstance(node[0],str):
        return node[0]
    return str(node)
data=load(sys.argv[1])
root=parse(data)
# root is ('AND',[kids]) tuple-ish
def show(n,d=0):
    if isinstance(n,tuple) and n[0]=='AND':
        print('  '*d+'AND')
        for k in n[1]: show(k,d+1)
    else:
        print('  '*d+ (n[0] if isinstance(n,tuple) else str(n)))
show(root)
