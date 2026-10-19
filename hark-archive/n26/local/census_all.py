import json,collections
t=json.load(open('/workspace/work/dcp-n26/v3replay/V3-REPLAY-TREE.json'));N=t['nodes']
par={}
for i,x in enumerate(N):
    for k in x.get('children',[]): par[k]=i
def sub(r):
    c=collections.Counter();st=[r]
    while st:
        i=st.pop();c[N[i]['kind']]+=1;st+=N[i].get('children',[])
    return dict(c)
roots=[i for i in range(len(N)) if i not in par]
out={'nnodes':len(N),'roots':roots,'whole':{r:sub(r) for r in roots}}
op=[i for i,x in enumerate(N) if x['kind'] not in('SPLIT','FORCE','LOCAL-SLAB')]
out['other_kind_nodes']=op[:50];out['n_other']=len(op)
out['open_by_top']={}
for i in op:
    j=i
    while j in par and par[j]!=roots[0]: j=par[j]
    out['open_by_top'][j]=out['open_by_top'].get(j,0)+1
json.dump(out,open('census_all.json','w'),default=dict)
print(json.dumps(out,default=dict)[:1500])
