"""Parse emitted C450 SourceK GroupedC / Data / Segment Lean files (WIP snapshot) into JSON.
Read-only on the WIP sources; exact rationals kept as [num,den] strings."""
import re,json,sys,os,glob
from fractions import Fraction as F
W=sys.argv[1] if len(sys.argv)>1 else '/tmp/wip/lean/N11Formalization'
TERM=r'\(\(?(-?\d+):ℚ\)(?:/(\d+)\))?'
def terms(s):
    out=[]
    for m in re.finditer(TERM,s):
        out.append(F(int(m.group(1)),int(m.group(2) or 1)))
    return out
def qlit(s):
    s=s.strip()
    m=re.fullmatch(r'\(*(-?\d+)(?::ℚ)?\)*(?:/\(*(\d+)\)*)?\)*',s.replace(' ',''))
    if not m: raise ValueError(s)
    return F(int(m.group(1)),int(m.group(2) or 1))
def parse_lohi(stmt):
    # "... Qcell A B" where A,B rational literals
    t=stmt.split('Qcell',1)[1].strip()
    # split two top-level parenthesised terms
    parts=[];depth=0;cur=''
    for ch in t:
        if ch=='(' : depth+=1
        if ch==')' : depth-=1
        cur+=ch
        if depth==0 and cur.strip():
            if ch==')' or ch==' ':
                if cur.strip(): parts.append(cur.strip()); cur=''
    parts=[p for p in parts if p]
    return [qlit(p) for p in parts[:2]]
segs={}
for k in range(11,37):
    d=open(f'{W}/C450Source{k}Data.lean').read()
    sd=terms(re.search(r'def source%d : TenSeg := ⟨(.*)⟩'%k,d).group(1))
    assert len(sd)==10,(k,sd)
    cells=[]
    for c in range(1,33):
        fn=f'{W}/C450Source{k}GroupedC{c:02d}.lean'
        s=open(fn).read()
        q=terms(re.search(r'def Qcell : RatInterval := ⟨(.*)⟩',s).group(1))
        pk=[]
        for m in re.finditer(r'def packet(\d+) : Packet := ⟨(.*)⟩',s):
            v=terms(m.group(2)); assert len(v)==14,(fn,m.group(1),len(v)); pk.append(v)
        leaves={}
        for m in re.finditer(r'private theorem leaf(\d+) :\s*\n\s*CellBound source\d+ nn0 nn1 Qcell (.*?) :=\s*\n\s*cell_of_packet source\d+ nn0 nn1 packet(\d+) valid(\d+)',s):
            assert m.group(1)==m.group(3)==m.group(4)
            leaves[int(m.group(1))]=parse_lohi('Qcell '+m.group(2))
        nodes=[]
        for m in re.finditer(r'private theorem (node\d+_\d+) :\s*\n\s*CellBound source\d+ nn0 nn1 Qcell (.*?) :=\s*\n\s*cell_join (\w+) (\w+)',s):
            nodes.append([m.group(1),[str(x) for x in parse_lohi('Qcell '+m.group(2))],m.group(3),m.group(4)])
        bound=re.search(r'theorem bound : CellBound source\d+ nn0 nn1 Qcell \(31/50\) \(69/50\) := (\w+)',s)
        nvalid=len(re.findall(r'theorem valid\d+ : Valid source%d packet\d+ := by\s*\n\s*constructor <;> \(try unfold RatInterval.Contains\) <;> decide \+kernel'%k,s))
        cells.append(dict(q=[str(x) for x in q],packets=[[str(x) for x in p] for p in pk],
            leaves={i:[str(x) for x in v] for i,v in leaves.items()},nodes=nodes,
            bound=bound.group(1) if bound else None,nvalid=nvalid,bytes=len(s)))
    segs[k]=dict(seg=[str(x) for x in sd],cells=cells)
dd=open(f'{W}/DSHTenBoundaryData.lean').read()
body=dd[dd.index('def c450Segs : List TenSeg := ['):]
body=body[:body.index('\n]')+2]
REC=r'\{([^}]*)\}'
FIELDS=['eLo','eHi','a0','a1','a2','a3','b0','b1','b2','b3']
def rec(txt):
    d={}
    for m in re.finditer(r'(\w+) := \((-?\d+) : ℚ\)(?: / (\d+))?',txt):
        d[m.group(1)]=F(int(m.group(2)),int(m.group(3) or 1))
    return [d[f] for f in FIELDS]
allsegs=[rec(m.group(1)) for m in re.finditer(REC,body)]
json.dump(dict(segs=segs,c450Segs=[[str(x) for x in s] for s in allsegs]),open(sys.argv[2] if len(sys.argv)>2 else 'c450.json','w'))
print('segments',len(segs),'c450Segs',len(allsegs),[len(s) for s in allsegs][:3])
print('packets',{k:sum(len(c['packets']) for c in v['cells']) for k,v in segs.items()})
