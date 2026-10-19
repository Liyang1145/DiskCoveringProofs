"""Direct-leaf face plane trees for a table. Usage: gen_face_trees.py <tab> <margin> [faces...]. Resumable, atomic."""
import sys,json,math,time,os
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent)); import rep_tables as RT, face_kernel as FK
ROOT=Path(__file__).parent.parent
jobs={'rep1':(2,1,'q1bal'),'q0m2':(0,2,'q0'),'rep7':(0,7,'q1bal')}
tab=sys.argv[1]; margin=float(sys.argv[2]); maxn=int(os.environ.get('MAXN','60000'))
start,k,cls=jobs[tab]; T=RT.build(start,k,cls)
sig=(RT.sigma if cls=='q1bal' else (lambda v:v))
hmap={tuple(sorted(sig(v) for v in f)):T['hist_upper'][f'face{t}'] for t,f in enumerate(T['faces_h'])}
path=ROOT/'data'/f'face_trees_{tab}.json'; res=json.loads(path.read_text()) if path.exists() else {}
todo=[tuple(map(int,a.split(','))) for a in sys.argv[3:]] or sorted(T['faces'])
fr=lambda x:f'{x.numerator}/{x.denominator}'
for f in todo:
  key=','.join(map(str,f))
  if key in res and res[key]['ok']: continue
  c=T['faces'][f]; M=F(math.ceil((hmap[f]+margin)*10**6),10**6); t=time.time()
  leaves,n=FK.gen_tree_grad(c,M,max_nodes=maxn)
  rec=dict(face=key,M=fr(M),hist_upper=hmap[f],ok=leaves is not None,nodes=n,sec=round(time.time()-t,1),
           coeff={x:[fr(v) for v in c[x]] for x in 'pqb'},
           leaves=[[kind,[fr(B[0][0]),fr(B[0][1]),fr(B[1][0]),fr(B[1][1])]] for kind,B in (leaves or [])])
  res[key]=rec; tmp=str(path)+'.tmp'; open(tmp,'w').write(json.dumps(res)); os.replace(tmp,path)
  with open(ROOT/'ledger.jsonl','a') as L: L.write(json.dumps(dict(item=f'facetree_{tab}_{key}',ok=rec['ok'],leaves=len(rec['leaves']),nodes=n,M=rec['M'],sec=rec['sec'],kind='python-exact-prevalidation'))+'\n')
  print(tab,key,rec['ok'],len(rec['leaves']),n,rec['M'],rec['sec'],flush=True)
