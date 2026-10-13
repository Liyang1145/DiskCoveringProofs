"""Bounded diagnostic of NEW inward-switch coupling, no certificate."""
from pathlib import Path
import math,json
from scipy.optimize import minimize_scalar
P=Path(__file__).parent;s=(P/'exchange_middle_inward_dual.py').read_text();marker='\n# Finite LP planes';assert s.count(marker)==1
ns={'__file__':str(P/'exchange_middle_inward_dual.py')};exec(s.split(marker)[0],ns)
np=ns['np'];value=ns['value'];R=.38;tau=75/76

def radius_interval(b):
 c=math.cos(b);D=c*c-R*R*tau*tau
 if D<0:return None
 root=math.sqrt(D);lo=R*tau*tau/(c+root);hi=min(1.,c/R,(c+root)/R)
 return (lo,hi) if lo<=hi else None

def sw_oracle(fi,z):
 def solve(b):
  seg=radius_interval(b)
  if seg is None:return None
  lo,hi=seg;c=value(fi,[b,0],z);f1=value(fi,[b,1],z)-c;fh=value(fi,[b,.5],z)-c;A=2*f1-4*fh;B=f1-A;ts=[lo,hi]
  if A<0 and lo<-B/(2*A)<hi:ts.append(-B/(2*A))
  t=max(ts,key=lambda t:A*t*t+B*t);return [b,t],value(fi,[b,t],z)
 # coarse subdivisions seed every possible branch; still numerical, not proof.
 grid=np.linspace(0,math.acos(R*tau),301);choices=[s for b in grid if (s:=solve(b)) is not None]
 for j in range(1,len(grid)-1):
  ss=solve(grid[j]);sl=solve(grid[j-1]);sr=solve(grid[j+1])
  if ss is not None and all(v is None or ss[1]>=v[1] for v in [sl,sr]):
   sol=minimize_scalar(lambda b:-solve(b)[1] if solve(b) else 1e3,bounds=(grid[j-1],grid[j+1]),method='bounded',options={'xatol':1e-13});choices.append(solve(sol.x))
 return max(choices,key=lambda s:s[1])
if __name__=='__main__':
 history=json.loads((P/'middle_inward_fiber_exchange_history.json').read_text());row=min(history,key=lambda r:r['continuous_numeric']);z=np.array(row['z']);out=[]
 for i in range(9):
  x,v=sw_oracle(11+i,z);out.append({'switch':i,'x':x,'new_numeric':v,'old_numeric':row['factor_values'][11+i]});print(out[-1],flush=True)
 total=row['continuous_numeric']+sum(r['new_numeric']-r['old_numeric'] for r in out)
 result={'scope':'new switch constraint diagnostic, otherfactor oraclevalues still numeric','old_total':row['continuous_numeric'],'new_total':total,'rows':out,'source_round':row['round']};(P/'switch_coupling_probe.json').write_text(json.dumps(result,indent=2));print('TOTAL',total,flush=True)
