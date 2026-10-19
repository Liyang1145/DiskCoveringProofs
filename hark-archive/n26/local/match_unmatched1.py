import json,glob,os
from fractions import Fraction as F
d=json.load(open('lleaf_boxes_missing.json'))
m={k:v for k,v in d['missing'].items() if v['top']==1}
P=lambda s:F(s)
res=[]
for p in [x for x in d['disk_unmatched_files'] if '/1/' in x]:
    fp=glob.glob('../**/'+p,recursive=True)[0]
    g=json.load(open(fp));lo=[P(str(x)) for x in g['lower']];hi=[P(str(x)) for x in g['upper']]
    for k,v in m.items():
        a=[P(x) for x in v['lo']];b=[P(x) for x in v['hi']]
        if len(a)!=len(lo):continue
        inter=all(max(l,x)<min(h,y) for l,h,x,y in zip(lo,hi,a,b))
        cont=all(l<=x and y<=h for l,h,x,y in zip(lo,hi,a,b))
        if inter: res.append((p,k,'contains' if cont else 'overlap'))
print(res); json.dump(res,open('match_unmatched1.json','w'))
