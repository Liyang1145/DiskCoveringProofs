"""Subtree census of replay-tree node 28 (root28): leaf kinds, depth, FORCE/LOCAL-SLAB counts, no OPEN."""
import json,collections,sys
t=json.load(open('/workspace/work/dcp-n26/v3replay/V3-REPLAY-TREE.json'));N=t['nodes']
root=int(sys.argv[1]) if len(sys.argv)>1 else 28
c=collections.Counter();maxd=0;ax=collections.Counter();st=[(root,0)]
while st:
    i,d=st.pop();x=N[i];maxd=max(maxd,d);c[x['kind']]+=1
    if x['kind']=='SPLIT':
        ax[x['axis']]+=1;st+=[(k,d+1) for k in x['children']]
print(json.dumps({'root':root,'kinds':c,'maxdepth':maxd,'split_axes':ax},default=dict))
