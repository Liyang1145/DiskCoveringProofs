"""Full retained436: bounded all-face factor-dual proposals and24000 totalbox splits per negativeproposal."""
from all_face_consistency_probe import solve
from all_face_consistency_certificate import *
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());data=json.loads((P/'shared-radius-retained.json').read_text())['retained'];out=[];start=time.time()
 with(P/'all-face-consistency-catalogue.jsonl').open('w')as stream:
  for item in data:
   fam=item['family'];idx=item['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});proposal=solve(q,edges,faces);proposal.update(family=fam,index=idx);row=prepare(q,edges,faces,proposal)
   cert=certify(q,edges,faces,row,24000)if proposal['sampled_lp_not_bound']<0 else{'status':'inconclusive','reason':'sampledLPnotnegative'};rec={'row':row,'certificate':cert,'sampled_lp_not_bound':proposal['sampled_lp_not_bound']};out.append(rec);stream.write(json.dumps(rec)+'\n');stream.flush();sc.cache_clear();costerm.cache_clear()
   if len(out)%10==0:print('processed',len(out),'excluded',sum(x['certificate']['status']=='excluded'for x in out),'seconds',time.time()-start,flush=True)
 (P/'all-face-consistency-catalogue.json').write_text(json.dumps({'status':'interval_factor_dual_catalogue_pending_replay','runs':out},indent=2));print('DONE',len(out),sum(x['certificate']['status']=='excluded'for x in out),time.time()-start,flush=True)
