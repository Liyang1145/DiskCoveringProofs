import json,sys,math
from fractions import Fraction as F
B=json.load(open('boxes.json'))['boxes']
for t in sys.argv[1:]:
    st=json.load(open(f'subtrees/{t}.json'))
    T=B[t];W=[F(h)-F(l) for l,h in zip(T['lo'],T['hi'])]
    def lv(lo,hi): return sum(math.log(float((F(h)-F(l))/w)) for l,h,w in zip(lo,hi,W) if w>0)
    pend=[math.exp(lv(s[1],s[2])) for s in st['stack']]
    print(t,'pending',len(pend),'pending vol frac %.3e'%sum(pend),'nodes',len(st['nodes']))
