"""Exact-rational perturbed cover + directed interval distinct endpoint radii.
Coverage follows certified upper witness +1e-6 Lipschitz displacement, not sampled check.
"""
import json,math
from pathlib import Path
from mpmath import iv
iv.dps=45;P=Path(__file__).parent
raw=json.loads(Path('n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
C=[[iv.mpf(int(v))/10**17 for v in row] for row in raw['centers_scaled_1e17']]
C[7][0]+=iv.mpf(1)/10**6
rings=sorted([i for i in range(11) if i not in [0,2]],key=lambda i:math.atan2(float(C[i][1].mid),float(C[i][0].mid)))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def sub(a,b):return [x-y for x,y in zip(a,b)]
def ds(a,b):return dot(sub(a,b),sub(a,b))
R=iv.mpf(19)/50
assert all(dot(C[i],C[i]).b<(1-R*R).a for i in rings)
S=[]
for t,i in enumerate(rings):
 j=rings[(t+1)%9];d=sub(C[j],C[i]);norm=iv.sqrt(dot(d,d));n=[d[1]/norm,-d[0]/norm];m=[(x+y)/2 for x,y in zip(C[i],C[j])];mn=dot(m,n);h=-mn+iv.sqrt(mn*mn+1-dot(m,m));p=[m[k]+h*n[k] for k in range(2)]
 rho2=ds(p,C[i]);assert abs(ds(p,C[j])-rho2).b<iv.mpf('1e-40').a
 assert all(ds(p,C[k]).a>rho2.b for k in range(11) if k not in [i,j])
 S.append((i,j,p,rho2))
idx=rings.index(7);a=S[(idx-1)%9][3];b=S[idx][3]
assert (a-b).a>0 or(a-b).b<0
T=iv.mpf('0.3799838531198387090485182');assert (T+iv.mpf(1)/10**6).b<R.a
out={'perturbed_site_original_index':7,'dx_exact':'1/1000000','coverage_upper':str(T+iv.mpf(1)/10**6),'cover_radius_threshold':'19/50','inward_norm_test_all_rings':True,'all_adjacent_switches_strict_nearest':True,'left_radius_squared':str(a),'right_radius_squared':str(b),'left_minus_right_squared':str(a-b),'coverage_source':'C529 exact threshold for integer/1e17 witness + coordinate-displacement Lipschitz inequality','statement':'At r=.38 a genuine inward-root cover has unequal previous/next switch radii. Diagonal u=v is NOT universally necessary.'}
(P/'unequal_switch_radii_control.json').write_text(json.dumps(out,indent=2));print(out)
