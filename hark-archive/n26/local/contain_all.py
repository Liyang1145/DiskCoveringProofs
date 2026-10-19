import json,glob
from fractions import Fraction as F
B=json.load(open('lleaf_boxes.json'))
print(type(B),len(B))
miss=json.load(open('lleaf_boxes_missing.json'))['missing']
def box(v):return [F(x) for x in v['lo']],[F(x) for x in v['hi']]
L=B['leaves']
miss_ids=set(miss)
cov=[k for k in L if k not in miss_ids]
print(len(cov),'non-missing')
cb={k:box(L[k]) for k in cov}
mb={k:box(miss[k]) for k in miss}
hit={}
for k,(lo,hi) in mb.items():
  for c,(clo,chi) in cb.items():
    if all(a<=b for a,b in zip(clo,lo)) and all(x<=y for x,y in zip(hi,chi)):
      hit[k]=c;break
out={'n_missing':len(mb),'contained_in_covered':len(hit),'ids':hit}
json.dump(out,open('contain_all.json','w'))
print(out['n_missing'],out['contained_in_covered'])
