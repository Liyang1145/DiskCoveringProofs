"""Exact convex combinations of independently valid normalized energy lower bounds."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,sys
from verify_fresh_kernels import verify
from verify_kernels import model_gate,demand

HERE=Path(__file__).resolve().parent
leaf=int(sys.argv[1]) if len(sys.argv)>1 else 2136
weight=Q(sys.argv[2]) if len(sys.argv)>2 else Q(1,2)
label=sys.argv[3] if len(sys.argv)>3 else 'mix50'
demand(0<=weight<=1,'convex combination weight')
model=json.loads((HERE/'RECOVERED-PHYSICAL-GRAPH.json').read_text());edges=model_gate(model)
GRID=10**50;result=[];descriptor=[]
for owner in (16,25):
    sources=[HERE/'fresh-kernels'/('leaf-'+str(leaf)+suffix+'-owner-'+str(owner)+'.json') for suffix in ('','-v01')]
    components=[verify(path,edges) for path in sources]
    allpairs=[{(i,j):int(lo) for i,j,lo,_ in kernel['pairs']} for kernel in components]
    pairs=[]
    for i in range(16):
        for j in range(i+1,16):
            value=weight*allpairs[0].get((i,j),0)+(1-weight)*allpairs[1].get((i,j),0)
            lower=value.numerator//value.denominator
            if lower:pairs.append([i,j,str(lower),str(lower)])
    value=weight*int(components[0]['constant_lower'])+(1-weight)*int(components[1]['constant_lower'])
    lower=value.numerator//value.denominator
    meta={'origin_owner':owner,'weights':[str(weight),str(1-weight)],
        'components':[{'file':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sources]}
    descriptor.append(meta)
    result.append({'leaf_index':leaf,'origin_owner':owner,'pairs':pairs,'constant_lower':str(lower),
        'coefficient_denominator':str(GRID),'reference_turns':components[0]['reference_turns'],
        'proof_type':'convex-mixture-of-verified-normalized-energy-lower-bounds',
        'components':meta,'source_kernel_sha256':hashlib.sha256(json.dumps(meta,sort_keys=True).encode()).hexdigest()})
out={'leaf_index':leaf,'origin_owner_alternatives':[16,25],'kernels':result,
     'convex_combination_checked':True,'global_optimality_proved':False}
path=HERE/'fresh-kernels'/('leaf-'+str(leaf)+'-'+label+'-VERIFIED.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print('PASS exact convex energy combination',leaf,label,str(weight))
