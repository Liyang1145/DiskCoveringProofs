"""One convexsolve+10vertex bound perretainedq10 graph; bounded112, proposals only."""
from anchor_simplex_probe import case,P,json
import time
start=time.time();ret=json.loads((P/'face-support-exchange-retained.json').read_text())['retained'];D=json.loads((P/'k10-catalogue-corrected.json').read_text());out=[]
for key in ret:
 if key['family']!='10/4':continue
 idx=key['index'];row=case('q10-'+str(idx),10,D['10/4'][idx]['faces'],[[i,(i+1)%10]for i in range(10)]);row.update(family='10/4',index=idx);out.append(row);(P/'anchor-simplex-q10-catalogue-probe.json').write_text(json.dumps({'status':'numeric_proposals_only','runs':out,'seconds':time.time()-start},indent=2))
print('DONE',len(out),'numeric_taylor_negatives',sum(x['global_taylor_vertex_lower_proposal']>.33173203427623414 for x in out),'seconds',time.time()-start,flush=True)
