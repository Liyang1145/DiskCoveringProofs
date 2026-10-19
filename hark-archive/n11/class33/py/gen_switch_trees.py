"""Generate switch trees (direct leaves) for rep1 (q1Faces 1 4) and q0 m=2, Lean switch order j.
Bound M_j = ceil(hist_upper + margin, 1e-6). Output data/switch_trees_<tab>.json (leaves) atomically, ledger rows."""
import sys,json,math,time,os
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent)); import rep_tables as RT, switch_kernel as K
ROOT=Path(__file__).parent.parent
def up(x,den=10**6): return F(math.ceil(x*den),den)
jobs={'rep1':(2,1,'q1bal',F(2,10**5)),'q0m2':(0,2,'q0',F(2,10**3))}
for tab in sys.argv[1:]:
  start,k,cls,margin=jobs[tab]; T=RT.build(start,k,cls); off=2 if cls=='q1bal' else 1
  path=ROOT/'data'/f'switch_trees_{tab}.json'
  res=json.loads(path.read_text()) if path.exists() else {}
  for j in range(9):
    if str(j) in res: continue
    c=T['switches'][j]; hu=T['hist_upper'][f'switch{(j+off-1)%9}']
    M=up(hu+float(margin)); t=time.time()
    leaves,n=K.gen_tree(c,M)
    rec=dict(j=j,M=f'{M.numerator}/{M.denominator}',hist_upper=hu,nodes_visited=n,ok=leaves is not None,
             leaves=[[f'{a.numerator}/{a.denominator}',f'{b.numerator}/{b.denominator}'] for a,b in (leaves or [])],
             coeff={x:f'{v.numerator}/{v.denominator}' for x,v in c.items()},sec=round(time.time()-t,1))
    res[str(j)]=rec
    tmp=str(path)+'.tmp'; open(tmp,'w').write(json.dumps(res)); os.replace(tmp,path)
    with open(ROOT/'ledger.jsonl','a') as L: L.write(json.dumps(dict(item=f'switchtree_{tab}_{j}',ok=rec['ok'],leaves=len(rec['leaves']),M=rec['M'],sec=rec['sec'],kind='python-exact-prevalidation'))+'\n')
    print(tab,j,rec['ok'],len(rec['leaves']),rec['M'],rec['sec'],flush=True)
