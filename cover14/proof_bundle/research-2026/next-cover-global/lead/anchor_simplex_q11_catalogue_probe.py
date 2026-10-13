"""Bounded243 retainedq11 graphcentroidflows; noexclusionswithoutcertificates."""
from anchor_simplex_probe import case,P,json
import time
start=time.time();ret=json.loads((P/'anchor-concave-retained.json').read_text())['retained'];D=json.loads((P/'q11-pocket-catalogue.json').read_text());out=[]
for key in ret:
 if key['family']!='11/3':continue
 idx=key['index'];row=case('q11-'+str(idx),11,D['entries'][idx]['faces'],[[i,(i+1)%11]for i in range(11)]);row.update(family='11/3',index=idx);out.append(row);(P/'anchor-simplex-q11-catalogue-probe.json').write_text(json.dumps({'status':'numeric_proposals_only','runs':out,'seconds':time.time()-start},indent=2))
print('DONE',len(out),'numeric_taylor_negatives',sum(x['global_taylor_vertex_lower_proposal']>.33173203427623414 for x in out),'numeric_concave_proposals',sum(x['concave_vertex_lower_proposal']>.33173203427623414 for x in out),'seconds',time.time()-start,flush=True)
