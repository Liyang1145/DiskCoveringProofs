"""Bounded numerical attack on hub vertical concavity/gradient, not proof."""
import attack_nested_frozen as ref
import interval_joint_patch as k
import numpy as np, math,json
z=[float(x.mid)for x in k.z];R=.38;rng=np.random.default_rng(1516);rows=[]
for it in range(500):
 data=ref.evaluate([rng.uniform(.375,.38),*rng.uniform(.02,.98,3)],True)
 if data is None:continue
 r,b1,b2,_,_,qa,_=data['chart'];delta=b1-qa*(b1+b2);s=math.sqrt(1-r*r);disc=s*s*math.cos(delta)**2-2*r*(1-r)
 lo=max(2*r*abs(math.sin(delta)),s*math.cos(delta)-math.sqrt(disc));hi=min(2*r*math.sin(2*b1-delta),2*r*math.sin(2*b2+delta),s*math.cos(delta)+math.sqrt(disc))
 H=rng.uniform(lo,hi);v=H*math.cos(delta);t=H*math.sin(delta);htt=0;gv=r*(math.sin(b1)**2+math.sin(b2)**2);gt=r*(math.sin(b2)*math.cos(b2)-math.sin(b1)*math.cos(b1))
 for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
  X=v-r*math.sin(2*b);Y=2*r*math.sin(b)**2+sg*t;L=math.hypot(X,Y);beta=bb/(4*R*R);gamma=gg/(2*R)
  htt+=2*beta+gamma*X*X/L**3-2*a*X*Y/L**4
  gv+=-a*Y/L**2+(2*beta+gamma/L)*X
  gt+=sg*(a*X/L**2+(2*beta+gamma/L)*Y)
 T=b1+b2;D=b1-b2;rv=2*r*math.sin(T)*math.cos(D);rt=2*r*math.sin(T)*math.sin(D);toward=gv*(rv-v)+gt*(rt-t)
 rows.append({'toward':toward,'boxpoint':[r,b1,b2,v,t],'htt':htt,'gv':gv,'gt':gt})
out={'scope':'boundedcounterexample_search_numeric_only','points':len(rows),'highbear_min_toward':min((q for q in rows if min(q['boxpoint'][1:3])>=.9),key=lambda q:q['toward']),'min_toward':min(rows,key=lambda q:q['toward']),'min_htt':min(rows,key=lambda q:q['htt']),'max_htt':max(rows,key=lambda q:q['htt']),'min_gv':min(rows,key=lambda q:q['gv']),'max_gv':max(rows,key=lambda q:q['gv'])};(k.P/'cartesian_curvature_probe.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
