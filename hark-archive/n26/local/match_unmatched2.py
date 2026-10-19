import json,glob
from fractions import Fraction as F
d=json.load(open('lleaf_boxes_missing.json'))
m=d['missing']
res=[]
for p in [x for x in d['disk_unmatched_files'] if '/28/' in x]:
    fp=glob.glob('../**/'+p,recursive=True)[0]
    g=json.load(open(fp));lo=[F(str(x)) for x in g['lower']];hi=[F(str(x)) for x in g['upper']]
    for k,v in m.items():
        a=[F(x) for x in v['lo']];b=[F(x) for x in v['hi']]
        if len(a)!=len(lo):continue
        if all(max(l,x)<min(h,y) for l,h,x,y in zip(lo,hi,a,b)):
            res.append((p,k,'contains' if all(l<=x and y<=h for l,h,x,y in zip(lo,hi,a,b)) else 'overlap'))
print(res);json.dump(res,open('match_unmatched2.json','w'))
