"""Calibrate monotone root box instrument against independent angle-sum bisection; numeric controls only."""
from shared_radius_corner_certificate import *
import random

def root_angle(bs):
 if sum(bs)<=math.pi:return 1.
 if sum(bs)>=2*math.pi:return 0.
 lo,hi=0.,1.
 for _ in range(65):
  x=(lo+hi)/2;H=sum(math.atan2(math.sin(b),x-math.cos(b))for b in bs)
  if H>math.pi:lo=x
  else:hi=x
 return (lo+hi)/2
if __name__=='__main__':
 rng=random.Random(20260927);tested=0;min_gap=1.;tight=0
 for _ in range(1000):
  ll=[rng.randrange(1,63)for j in range(3)];hh=[min(64,l+rng.randrange(1,8))for l in ll];box=[(Q(l,64),Q(h,64))for l,h in zip(ll,hh)];X=radius_upper(box)
  for j in range(4):
   bs=[math.pi*(float(l)+(float(h-l)*rng.random()))for l,h in box]
   if sum(bs)>=2*math.pi:continue
   actual=root_angle(bs);assert actual<=float(X)+1e-13;min_gap=min(min_gap,float(X)-actual);tested+=1
  tight+=X<1
 rec=json.loads((P/'shared-radius-reopt-probe.json').read_text())['runs'][0];row=rec['row'];G=json.loads((P/'stress-barycentric-result.json').read_text());faces=[x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});cert=certify_pack(10,edges,faces,row,[14,15],12000);assert cert['status']!='excluded';out={'status':'numeric_root_control_interval_candidate_nonexclusion','tested_points':tested,'tightened_boxes':tight,'minimum_numeric_slack':min_gap,'candidate_interval_upper':cert['upper_display']};(P/'shared-radius-corner-control.json').write_text(json.dumps(out,indent=2));print(out)
