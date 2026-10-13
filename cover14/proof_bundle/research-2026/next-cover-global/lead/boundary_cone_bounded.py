"""Bounded numeric effect of boundaryradiuscone: candidate+six old factor-dualcontrols."""
from boundary_cone_dual_probe import *
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());data=json.loads((P/'all-face-consistency-probe.json').read_text())['runs'];G=json.loads((P/'stress-barycentric-result.json').read_text());out=[]
 for old in data:
  fam=old['family'];idx=old['index'];q=10 if fam=='candidate'else int(fam.split('/')[0]);faces=([x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]])if fam=='candidate'else(D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces']);edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});row=solve(q,edges,faces);row.update(family=fam,index=idx,old_sampled_lp=old['sampled_lp_not_bound']);out.append(row);print(fam,idx,'old',old['sampled_lp_not_bound'],'new',row['sampled_lp_not_bound'],flush=True)
 (P/'boundary-cone-bounded.json').write_text(json.dumps({'status':'numeric_only_boundary_cone_cap','runs':out},indent=2))
