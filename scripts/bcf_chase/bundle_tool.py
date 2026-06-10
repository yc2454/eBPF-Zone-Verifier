import struct, sys
HDR=16; ENT=28; MAGIC=0x42464342
def parse(fn):
    b=open(fn,'rb').read()
    magic,n,total,_=struct.unpack_from('<IIII',b,0)
    assert magic==MAGIC, hex(magic)
    ents=[]
    for i in range(n):
        off=HDR+ENT*i
        h,goff,glen,poff,plen,kind=struct.unpack_from('<QIIIII',b,off)
        goal=b[goff:goff+glen]; proof=b[poff:poff+plen]
        ents.append((h,kind,goal,proof))
    return ents
def build(ents):
    def a4(x): return (x+3)&~3
    n=len(ents); pbase=HDR+ENT*n
    # compute payload
    out=bytearray(); 
    out+=struct.pack('<IIII',MAGIC,n,0,0)
    cur=pbase
    offs=[]
    for h,kind,goal,proof in ents:
        goff=cur; gp=a4(len(goal)); poff=goff+gp; pp=a4(len(proof))
        offs.append((goff,poff)); cur=poff+pp
    for (h,kind,goal,proof),(goff,poff) in zip(ents,offs):
        out+=struct.pack('<QIIIII',h,goff,len(goal),poff,len(proof),kind)
    for h,kind,goal,proof in ents:
        out+=goal; out+=b'\0'*((4-len(goal)%4)%4)
        out+=proof; out+=b'\0'*((4-len(proof)%4)%4)
    struct.pack_into('<I',out,8,len(out))
    return bytes(out)
if __name__=='__main__':
    cmd=sys.argv[1]
    if cmd=='hashes':
        for h,k,g,p in parse(sys.argv[2]): print('%016x'%h)
    elif cmd=='clone':  # clone donor_bundle hashfile out -> bundle where EVERY hash is a clone of donor[0]
        donor=parse(sys.argv[2])[0]   # (h,kind,goal,proof); kind must be 2 (UNREACHABLE)
        hs=[l.strip() for l in open(sys.argv[3]) if l.strip()]
        ents=[(int(h,16), 2, donor[2], donor[3]) for h in hs]
        open(sys.argv[4],'wb').write(build(ents))
        import os
        print('cloned',len(ents),'entries bytes',os.path.getsize(sys.argv[4]))
    elif cmd=='pickx':  # pickx superset wantfile fakefile out -> real picks + cloned fakes (cond_hash overridden)
        sup=parse(sys.argv[2])
        want=[l.strip() for l in open(sys.argv[3]) if l.strip()]
        fakes=[l.strip() for l in open(sys.argv[4]) if l.strip()] if len(sys.argv)>4 and __import__('os').path.exists(sys.argv[4]) else []
        supmap={'%016x'%h:(h,k,g,p) for h,k,g,p in sup}
        ents=[supmap[w] for w in want if w in supmap]
        donor=ents[0] if ents else sup[0]   # clone donor's goal/proof/kind
        for f in fakes:
            ents.append((int(f,16), donor[1], donor[2], donor[3]))
        open(sys.argv[5],'wb').write(build(ents))
        import os
        print('pickx real',len([w for w in want if w in supmap]),'fake',len(fakes),'bytes',os.path.getsize(sys.argv[5]))
    elif cmd=='pick':  # pick superset hashfile out -> bundle of superset entries whose hash in hashfile
        sup=parse(sys.argv[2])
        want=set(l.strip() for l in open(sys.argv[3]) if l.strip())
        supmap={'%016x'%h:(h,k,g,p) for h,k,g,p in sup}
        ents=[supmap[w] for w in want if w in supmap]
        missing=[w for w in want if w not in supmap]
        open(sys.argv[4],'wb').write(build(ents))
        import os
        print('picked',len(ents),'of',len(want),'bytes',os.path.getsize(sys.argv[4]),'missing_from_superset',missing)
    elif cmd=='merge':  # base superset hashfile out  -> base entries + named hashes from superset
        base=parse(sys.argv[2]); sup=parse(sys.argv[3])
        want=set(l.strip() for l in open(sys.argv[4]) if l.strip())
        have=set('%016x'%h for h,_,_,_ in base)
        supmap={'%016x'%h:(h,k,g,p) for h,k,g,p in sup}
        added=0; notfound=[]
        ents=list(base)
        for w in want:
            if w in have: continue
            if w in supmap: ents.append(supmap[w]); have.add(w); added+=1
            else: notfound.append(w)
        open(sys.argv[5],'wb').write(build(ents))
        print('added',added,'total',len(ents),'notfound',notfound)

def parse_goal(goal):
    import struct
    root,n=struct.unpack_from('<II',goal,0); off=8; exprs=[]
    for i in range(n):
        code=goal[off]; vlen=goal[off+1]; params=struct.unpack_from('<H',goal,off+2)[0]; off+=4
        args=[struct.unpack_from('<I',goal,off+4*k)[0] for k in range(vlen)]; off+=4*vlen
        exprs.append((code,vlen,params,args))
    return root,exprs
