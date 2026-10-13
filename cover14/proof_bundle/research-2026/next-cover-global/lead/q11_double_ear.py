"""Exact rational arc-capacity exclusion: two vertex-disjoint all-ring triangles."""
import json,math
from fractions import Fraction as Q
from pathlib import Path
P=Path(__file__).resolve().parent
U=Q('0.33173203427623414')
def asin_bounds(x,N=100):
 # asin x=sum binom(2n,n)/(4^n(2n+1))*x^(2n+1), coefficients<=1.
 lo=sum((Q(math.comb(2*n,n),4**n*(2*n+1))*x**(2*n+1)for n in range(N)),Q(0))
 return lo,lo+x**(2*N+1)/(1-x*x)
a=asin_bounds(U);b=asin_bounds(2*U)
# Archimedean pi lower can be certified by Machin arctangent alternating series.
def atan_bounds(x,N=80):
 t=sum(((-1)**n*x**(2*n+1)/(2*n+1)for n in range(N)),Q(0));nxt=(-1)**N*x**(2*N+1)/(2*N+1)
 return min(t,t+nxt),max(t,t+nxt)
u=atan_bounds(Q(1,5));v=atan_bounds(Q(1,239));pilo=16*u[0]-4*v[1]
margin=2*pilo-4*b[1]-10*a[1];assert margin>0
D=json.loads((P/'q11-pocket-catalogue.json').read_text());keep=[];removed=[];hist={}
for idx,e in enumerate(D['entries']):
 ears=[set(f)for f in e['faces']if max(f)<11]
 pair=next(((sorted(x),sorted(y))for i,x in enumerate(ears)for y in ears[i+1:]if not x&y),None)
 if pair:removed.append({'index':idx,'disjoint_ear_faces':pair})
 else:keep.append(idx)
 key=str(len(e['chord_middle_representative']));hist.setdefault(key,[0,0]);hist[key][int(pair is not None)]+=1
out={'status':'exact_arc_capacity_pruning','threshold':str(U),'margin_exact_lower':str(margin),'margin_decimal_display':float(margin),'before':len(D['entries']),'retained_count':len(keep),'removed_count':len(removed),'retained_indices':keep,'removed_witnesses':removed,'by_chord_count_retained_removed':hist,'scope':'q11 only; excludes two vertex-disjoint all-ring faces using owned-arc capacity, not all candidate graphs'}
(P/'q11-double-ear-pruning.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in('retained_indices','removed_witnesses','margin_exact_lower')})
