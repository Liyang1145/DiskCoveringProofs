import json,sys;from fractions import Fraction as F
import propose as PP
th=[F(x) for x in json.load(open('../kkt2_122.json'))['z'][:15]]
B=json.load(open('boxes.json'))['boxes'];L=B['59']
st=json.load(open('subtrees/135.json'));s=st['stack'][-1]
dig=[(F(a)+F(b))/2 for a,b in zip(s[1],s[2])]
def R(p):
    v,G,Fl=PP.propose(p,p); c,m=PP.rationalize(p,p,G,Fl); return v-float(PP.RUP), float(m)
print('theta*',R(th))
p=list(th);p[13]=F(L['hi'][13]);print('proj13',R(p))
for k in [1,2,4,8]:
  p=list(th);p[13]=th[13]+k*(F(L['hi'][13])-th[13]);print('ax13 x',k,R(p))
print('dig',R(dig))
