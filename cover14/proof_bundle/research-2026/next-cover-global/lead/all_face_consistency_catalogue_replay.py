"""Stream independent Fraction replay; negative proofs persisted percase, fullcountonlyafter producerDONE."""
from all_face_consistency_fraction_replay import *
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());out=[];seen=set();start=time.time();dst=P/'all-face-consistency-catalogue-fraction.jsonl'
 if dst.exists():
  for line in dst.read_text().splitlines():
   rec=json.loads(line);out.append(rec);seen.add((rec['family'],rec['index']))
 with dst.open('a')as stream:
  while True:
   source=P/'all-face-consistency-catalogue.jsonl';lines=source.read_text().splitlines();pending=[]
   for line in lines:
    try:rec=json.loads(line)
    except json.JSONDecodeError:continue
    row=rec['row'];key=(row['family'],row['index'])
    if rec['certificate']['status']=='excluded'and key not in seen:pending.append(rec)
   for rec in pending:
    row=rec['row'];cert=rec['certificate'];fam=row['family'];idx=row['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});b=verify_all(q,edges,faces,row,cert);assert b[1]<0;ans={'family':fam,'index':idx,'upper_exact':str(b[1]),'upper_display':float(b[1])};out.append(ans);seen.add((fam,idx));stream.write(json.dumps(ans)+'\n');stream.flush();sc.cache_clear();print('replayed',len(out),fam,idx,float(b[1]),'seconds',time.time()-start,flush=True)
   if (P/'all-face-consistency-catalogue.json').exists():
    full=json.loads((P/'all-face-consistency-catalogue.json').read_text())['runs'];expected={(x['row']['family'],x['row']['index'])for x in full if x['certificate']['status']=='excluded'}
    if expected<=seen:
     assert expected==seen;(P/'all-face-consistency-catalogue-fraction-replay.json').write_text(json.dumps({'status':'independent_fraction_full_catalogue_replay','producer_count':len(full),'runs':out},indent=2));print('DONE',len(out),time.time()-start,flush=True);break
   time.sleep(20)
