"""Exact tree-integrity check of replay-tree node 28 subtree: binary SPLITs, each node reached once,
and along every path the split mids on each axis nest strictly (left child <=mid, right >=mid, interval nonempty
=> no mid equals a boundary already imposed). Fractions exact."""
import json,sys
from fractions import Fraction as F
t=json.load(open('/workspace/work/dcp-n26/v3replay/V3-REPLAY-TREE.json'));N=t['nodes']
root=int(sys.argv[1]) if len(sys.argv)>1 else 28
seen=set();bad=[];leaves=0;st=[(root,{})]
while st:
    i,iv=st.pop()
    if i in seen: bad.append(('dup',i));continue
    seen.add(i);x=N[i]
    if x['kind']!='SPLIT': leaves+=1;continue
    if len(x['children'])!=2: bad.append(('arity',i));continue
    a=x['axis'];m=F(x['mid']);lo,hi=iv.get(a,(None,None))
    if (lo is not None and m<=lo) or (hi is not None and m>=hi): bad.append(('mid_out',i,a,str(m)));continue
    l,r=x['children']
    st.append((l,{**iv,a:(lo,m)}));st.append((r,{**iv,a:(m,hi)}))
res={'root':root,'nodes':len(seen),'leaves':leaves,'bad':bad[:10],'nbad':len(bad),'pass':not bad}
print(json.dumps(res))
open('/workspace/work/dcp-n26/local/tree28_integrity.json','w').write(json.dumps(res))
