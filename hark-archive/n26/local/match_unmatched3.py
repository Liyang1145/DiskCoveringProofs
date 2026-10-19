import json,glob
from fractions import Fraction as F
d=json.load(open('lleaf_boxes_missing.json'))
m=d['missing']
done=set(x[1] for x in json.load(open('match_unmatched2.json')))
print(len(m),len(d['disk_unmatched_files']),d['disk_unmatched_files'][:3])
res=[]
for p in d['disk_unmatched_files']:
    fp=glob.glob('../**/'+p,recursive=True)
    if not fp: continue
    g=json.load(open(fp[0]));lo=[F(str(x)) for x in g['lower']];hi=[F(str(x)) for x in g['upper']]
    for k,v in m.items():
        a=[F(x) for x in v['lo']];b=[F(x) for x in v['hi']]
        if len(a)!=len(lo):continue
        if all(max(l,x)<min(h,y) for l,h,x,y in zip(lo,hi,a,b)):
            res.append((p,k,'contains' if all(l<=x and y<=h for l,h,x,y in zip(lo,hi,a,b)) else 'overlap'))
print(len(res),res[:10]);json.dump(res,open('match_unmatched3.json','w'))
