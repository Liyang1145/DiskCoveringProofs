"""Checker B for node-59 pilot shells: re-derives geometry from boxes.json (own code), checks coverage of b-range, runs local/certB.check_leaf (mpmath iv). Resumable."""
import sys,json,os,time,glob
sys.path.insert(0,'/workspace/work/dcp-n26/local')
import certB
from certB import F,CS,L0,TAU,V,check_leaf
ROOT='/workspace/work/dcp-n26/v3replay'
B=json.load(open(ROOT+'/boxes.json'))['boxes']['59']; LO=[F(x) for x in B['lo']]; HI=[F(x) for x in B['hi']]
R0=max(max(c-l,h-c) for l,h,c in zip(LO,HI,CS))
MU=F(11,200); M=int(sys.argv[2]) if len(sys.argv)>2 else 12
def Q(m):
    r=R0/2**m; return [max(l,c-r) for l,c in zip(LO,CS)],[min(h,c+r) for h,c in zip(HI,CS)]
def slabs(m):
    a,b=Q(m); c,d=Q(m+1); a=list(a); b=list(b); out=[]
    for k in range(15):
        if a[k]<c[k]: h=list(b); h[k]=c[k]; out.append((list(a),h)); a[k]=c[k]
        if b[k]>d[k]: l=list(a); l[k]=d[k]; out.append((l,list(b))); b[k]=d[k]
    return out
assert Q(0)==(LO,HI)
T0=time.time(); BUD=float(sys.argv[1])
st=ROOT+'/verB59.json'; S=json.load(open(st)) if os.path.exists(st) else {'done':{}}
tot=0
for m in range(M):
    for s,(lo,hi) in enumerate(slabs(m)):
        tot+=1; key=f'{m}_{s}'
        if key in S['done']: continue
        if time.time()-T0>BUD: print('budget stop; verified',len(S['done'])); sys.exit(0)
        d=json.load(open(f'{ROOT}/lleaves/59pilot/m{m}_s{s}.json'))
        assert [F(x) for x in d['lower']]==lo and [F(x) for x in d['upper']]==hi,key
        b1=sum(min(v*(a-c),v*(b-c)) for v,a,b,c in zip(V,lo,hi,CS)); b2=sum(max(v*(a-c),v*(b-c)) for v,a,b,c in zip(V,lo,hi,CS))
        ps=d['pieces']; assert F(ps[0]['ba'])<=b1 and F(ps[-1]['bb'])>=b2
        for p,q in zip(ps,ps[1:]): assert p['bb']==q['ba']
        worst=None
        for p in ps:
            assert 'OPEN' not in p
            kap=F(p['kappa']); w=[a+kap*t for a,t in zip(L0,TAU)]; assert all(x>=0 for x in w)
            bd=check_leaf(w,lo,hi,F(p['ba']),F(p['bb']),MU)
            assert bd is not None and bd>0,(key,p['ba'])
            worst=bd if worst is None else min(worst,bd)
        S['done'][key]={'pieces':len(ps),'min':str(worst),'min_over_rho2':float(worst/(R0/2**m)**2)}
        json.dump(S,open(st+'.tmp','w')); os.replace(st+'.tmp',st)
        open('/workspace/work/dcp-n26/ledger.jsonl','a').write(json.dumps({'event':'node59-pilot-B','key':key,'pieces':len(ps),'min':float(worst)})+'\n')
print('ALL',tot,'verified',len(S['done']),'min/rho2',min(v['min_over_rho2'] for v in S['done'].values()))
