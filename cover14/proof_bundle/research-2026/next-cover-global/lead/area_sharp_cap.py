"""Exact bounded-cap simplex maximum applied to already saved2042 planes."""
import json
from area_safe_certificate import I,Q,S,PI,L,U,trig,cap_minus_pi,P
R=2*PI-9*L
assert R.lo>0 and (L-R).lo>0
sinL=2*I(U)*(1-I(U)**2).sqrt();sinR,_=trig(R)
sharp_cap_minus_pi=-(9*sinL+sinR)/2
change=sharp_cap_minus_pi-cap_minus_pi
rows=[json.loads(x)for x in(P/'area-safe-catalogue.jsonl').read_text().splitlines()];out=[];counts={}
for row in rows:
 lo,hi=map(Q,row['area_minus_pi_enclosure']);old=I(I(lo).lo,I(hi).hi,True);new=old+change
 status='excluded'if new.hi<0 else'inconclusive';fam=row['family'];counts.setdefault(fam,{});counts[fam][status]=counts[fam].get(status,0)+1
 out.append({'family':fam,'index':row['index'],'status':status,'newly_excluded':status=='excluded'and row['status']!='excluded','upper_exact':str(Q(new.hi,S)),'upper_display':new.hi/S})
(P/'area-sharp-cap.json').write_text(json.dumps({'status':'exact_interval','scope':'same2042supportingplanes, strongerboundarycap; nooptimizer rerun','residual_arc':R.dec(),'cap_decrease':(-change).dec(),'counts':counts,'runs':out},indent=2));print(counts);print('new',[(x['family'],x['index'])for x in out if x['newly_excluded']])
# Independent Fraction evaluationof thecap difference, applied to13 newexclusionstoredplanes.
from area_safe_fraction_replay import F,pi,L as LF,capminus,add,neg,mul,point,replay,div,sqrtv,trig as FT
RF=add(mul(point(F(2)),pi),neg(mul(point(F(9)),LF)))
# sin is increasingon R⊂(0,pi/2); endpointTaylorenclosures.
assert RF[0]>0 and RF[1]<pi[0]/2
sinRF=(FT(RF[0])[0][0],FT(RF[1])[0][1]);newcap=neg(mul(point(F(1,2)),add(mul(point(18*U),sqrtv),sinRF)))
from itertools import combinations
D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());checks=[]
for row,rec in zip(rows,out):
 if not rec['newly_excluded']:continue
 fam=row['family'];q=int(fam.split('/')[0]);idx=row['index'];faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)})
 t=list(map(F,row['rational_angles']));y=list(map(F,row['rational_node_potentials']));bound=add(replay(q,edges,t,y),add(newcap,neg(capminus)));assert bound[1]<0
 checks.append({'family':fam,'index':idx,'upper_display':float(bound[1]),'upper_rational_outward':str(F(-((-bound[1].numerator*10**30)//bound[1].denominator),10**30))})
(P/'area-sharp-cap-fraction-replay.json').write_text(json.dumps({'status':'independent_fraction_replay','runs':checks},indent=2));print('fractionreplay',len(checks))
