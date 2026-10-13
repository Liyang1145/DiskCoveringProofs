"""Bounded six-case sampled dual proposal test of normalized boundarycone cap. No certificates."""
from all_face_consistency_probe import *
from pathlib import Path
import inspect
source=inspect.getsource(solve).replace('def solve(q,edges,faces,nfg=11):','def cone_solve(q,edges,faces,nfg=11):')
source=source.replace("nf=len(faces);ne=len(edges);ee=","nf=len(faces);ne=len(edges);boundary={e for e in edges if sum(set(e)<=set(f) for f in faces)==1};ee=")
source=source.replace('for ts,A in samples:\n    mat[at,iw+f]=A','for ts,A in samples:\n    X=min([1.]+[1/max(1.,math.cos(ts[j])+r/math.sqrt(1-r*r)*math.sin(ts[j])) for j,e in enumerate(ee[f]) if e in boundary]); A=min(A,r*r*X*sum(math.sin(t) for t in ts))\n    mat[at,iw+f]=A')
source=source.replace('a=r*r*math.sin(t);mat[at,u]=-t;mat[at,v]=-t','a=r*r*math.sin(t)/(max(1.,math.cos(t)+r/math.sqrt(1-r*r)*math.sin(t)) if (u,v) in boundary else 1.);mat[at,u]=-t;mat[at,v]=-t')
exec(source)
if __name__=='__main__':
 start=time.time();D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());src=json.loads((P/'all-face-consistency-catalogue.json').read_text())['runs'];ret={(x['family'],x['index']) for x in json.loads((P/'all-face-consistency-full-retained.json').read_text())['retained']};sel=[]
 for fam in ['10/4','11/3']:
  a=[x for x in src if x['row']['family']==fam and (fam,x['row']['index'])in ret and 'upper_display'in x['certificate']];a.sort(key=lambda x:x['certificate']['upper_display']);sel+=a[:3]
 out=[]
 for old in sel:
  row=old['row'];fam=row['family'];idx=row['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});a=solve(q,edges,faces);b=cone_solve(q,edges,faces);b.update(family=fam,index=idx,old_sampled_lp=a['sampled_lp_not_bound'],old_interval_upper=old['certificate']['upper_display']);out.append(b);print(fam,idx,'old',a['sampled_lp_not_bound'],'new',b['sampled_lp_not_bound'],'seconds',time.time()-start,flush=True);(P/'boundary-cone-factor-probe.json').write_text(json.dumps({'status':'numeric_sampled_lp_proposals_not_bounds','runs':out},indent=2))
