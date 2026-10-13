"""Independent rational partition and edge-disjointness replay of face packs."""
from all_face_fraction_kernel import *
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());data=json.loads((P/'pack-reopt-probe.json').read_text())['runs'];rows={(x['row']['family'],x['row']['index']):x['row']for x in data};certs=[x['certificate']for x in data];out=[];start=time.time()
 for c in certs:
  if c['status']!='excluded':continue
  fam=c['family'];idx=c['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});row=rows[fam,idx];total=replay(q,edges,row);b=point(F(0));used=set()
  for part in c['parts']:
   ee={tuple(sorted(e))for e in combinations(faces[part['face']],2)};assert not used&ee;used|=ee;b=add(b,verify(q,edges,faces,row,part))
  b=rnd(sub(b,mul(point(F(len(c['parts'])-1)),total)));assert b[1]<0;out.append({'family':fam,'index':idx,'faces':[p['face']for p in c['parts']],'upper_display':float(b[1]),'upper_exact_outward':str(b[1]),'leaves':sum(len(p['leaves'])for p in c['parts'])});print('replayed',len(out),'seconds',time.time()-start,flush=True)
 (P/'pack-reopt-fraction-replay.json').write_text(json.dumps({'status':'independent_fraction_partition_and_edgedisjointness','runs':out},indent=2))
