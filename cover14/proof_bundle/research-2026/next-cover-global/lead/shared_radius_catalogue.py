"""Full573 bounded pass: common-radius local envelope, rational proposals, interval supports."""
from shared_radius_reopt_probe import optimize
from shared_radius_corner_certificate import *
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());tests=json.loads((P/'all-face-pack-catalogue.json').read_text())['runs'];ret={(x['family'],x['index'])for x in json.loads((P/'pack-reopt-retained.json').read_text())['retained']};out=[];start=time.time()
 with (P/'shared-radius-catalogue.jsonl').open('w') as stream:
  for test in tests:
   fam=test['family'];idx=test['index']
   if (fam,idx)not in ret:continue
   q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});pack=test.get('faces') or [p['face']for p in test.get('parts',[])];assert pack
   row=optimize(q,edges,faces,pack);row.update(family=fam,index=idx)
   if row['sampled_lp_not_bound']<0:cert=certify_pack(q,edges,faces,row,pack,6000)
   else:cert={'family':fam,'index':idx,'status':'inconclusive','reason':'sampled LP no negative proposal'}
   rec={'row':row,'certificate':cert};out.append(rec);stream.write(json.dumps(rec)+'\n');stream.flush();sc.cache_clear();costerm.cache_clear()
   if len(out)%20==0:print(len(out),'excluded',sum(x['certificate']['status']=='excluded'for x in out),'seconds',time.time()-start,flush=True)
 (P/'shared-radius-catalogue.json').write_text(json.dumps({'status':'interval_certificates_common_radius_envelope','runs':out},indent=2));print('DONE',len(out),sum(x['certificate']['status']=='excluded'for x in out),time.time()-start,flush=True)
