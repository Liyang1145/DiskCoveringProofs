"""Separate coarse LP underestimation from cube interval width; numeric only."""
from shared_radius_box_kernel import *
from scipy.optimize import differential_evolution

def area(ts):
 ss=sum(ts);a=sum(math.sin(t)for t in ts)
 if ss>2*math.pi:return -1e3
 old=float(U*U)*(a-.5*min(1-math.cos(t)for t in ts)*abs(ss-math.pi))
 if ss<=math.pi or a<1e-12:return old
 b=sum(math.sin(u+v)for u,v in combinations(ts,2));c=math.sin(ss);x0=max(0,min(1,(b+math.sqrt(max(0,b*b-4*a*c)))/(2*a)))
 return min(old,float(U*U)*x0*a)
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());data=json.loads((P/'shared-radius-reopt-probe.json').read_text())['runs'];out=[]
 for rec in [data[1],data[7]]:
  row=rec['row'];cert=rec['certificate'];fam=row['family'];idx=row['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});t=list(map(Q,row['rational_angles']));y=list(map(Q,row['rational_potentials']));total=verify(q,edges,t,y,Q(row['rational_nu']),Q(row['rational_lambda']));num=total.hi/S;parts=[]
  for part in cert['parts']:
   ee=[tuple(sorted(e))for e in combinations(faces[part['face']],2)];ps=[sum(y[v]for v in e)for e in ee];old=sum(edgeold(t[q+edges.index(e)],p).hi/S for e,p in zip(ee,ps));opt=differential_evolution(lambda ts:sum(float(p)*z for p,z in zip(ps,ts))-area(ts),[(0,math.pi)]*3,seed=130,maxiter=150,popsize=12,tol=1e-9);new=-opt.fun;num+=new-old;parts.append({'face':part['face'],'numeric_sup':new,'arg':list(opt.x)})
  v={'family':fam,'index':idx,'sample_lp':row['sampled_lp_not_bound'],'numeric_support_upper_NOT_certificate':num,'interval_upper':cert['upper_display'],'parts':parts};out.append(v);print(v,flush=True)
 (P/'shared-radius-support-diagnostic.json').write_text(json.dumps({'status':'numeric_only_support_probe','runs':out},indent=2))
