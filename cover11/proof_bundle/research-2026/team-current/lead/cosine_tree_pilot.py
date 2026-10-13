"""Bounded511-cell extension of saved exact stellar tree with cosine LP.
Three saved patches checked by exact vertex containment; every unresolved leaf retained.
"""
from cosine_envelope_lp_diagnostic import solve
from certify_cosine_envelope_cell import certify
from simplex_tree_pilot import *
import time

def patch(v):
 for j in range(9):
  t=F(3,5) if j in [0,1,2,5,6] else F(13,20) if j in [4,7] else F(3,4)
  if all(y[j]>=t for y in v):return 'C914-corner'+str(j)
 if all(min(y)>=F(31,450) for y in v):return 'C913'
 d=json.loads((P/'canonical_local_patch_certificate.json').read_text());c=[F(x) for x in d['center_y']];e=F(d['halfwidth_independent8'])
 if all(all(abs(y[i]-c[i])<=e for i in range(8)) for y in v):return 'C916'
 return None

def main():
 fields=json.loads((P/'energy_library.json').read_text())['fields'];old=json.loads((P/'adaptive_stellar_pilot.json').read_text());nodes=old['nodes'];seed=json.loads((P/'cosine_leaf_full_pilot.json').read_text());seenCert={r['node']:r['certificate'] for r in seed['leaves'] if r['status']=='certified'}
 for n in nodes:
  n['vertices']=[[F(x) for x in v] for v in n['vertices']];n['mass']=F(n['mass'])
  if n['id'] in seenCert:n.update({'status':'certified','certificate':seenCert[n['id']]})
 queue=deque(n['id'] for n in nodes if n['status']=='open');started=time.time();processed=0
 while queue and processed<511:
  idx=queue.popleft();n=nodes[idx];v=n['vertices'];processed+=1;pp=patch(v)
  if pp:n.update({'status':'certified','patch':pp});continue
  rr=solve(v,fields);n['numeric_lower']=rr['radius_lower_numeric']
  if rr['radius_lower_numeric']>.380001:
   rr.update({'cell':str(idx),'vertices':[[str(x) for x in y] for y in v]});cc=certify(rr,fields)
   if cc['certified_gt_19_50']:n.update({'status':'certified','certificate':cc});continue
  i,j,a,b=split(v);n.update({'status':'split','kind':'midpoint','edge':[i,j],'children':[len(nodes),len(nodes)+1]})
  for vv in [a,b]:
   ni=len(nodes);nodes.append({'id':ni,'depth':n['depth']+1,'mass':n['mass']/2,'vertices':vv,'status':'open'});queue.append(ni)
  if processed%50==0:print('processed',processed,'open',len(queue),'cert',sum(x['status']=='certified' for x in nodes),flush=True)
 # Verify ALL old stellar and new midpoint incidence. Geometric coverage uses ratio-minimum lemma.
 visited={0}
 for n in nodes:
  if n['status']!='split':continue
  if n['kind']=='midpoint':
   i,j,a,b=split(n['vertices']);assert [i,j]==n['edge'];parts=[(F(1,2),a),(F(1,2),b)]
  else:
   lam=[F(x) for x in n['lambda']];assert min(lam)>=0 and sum(lam)==1;p=[sum(lam[j]*n['vertices'][j][i] for j in range(9)) for i in range(9)];parts=[]
   for j,l in enumerate(lam):
    if not l:continue
    vv=[r[:] for r in n['vertices']];vv[j]=p;parts.append((l,vv))
  assert len(parts)==len(n['children'])
  for ch,(ratio,vv) in zip(n['children'],parts):
   assert ch not in visited;visited.add(ch);assert nodes[ch]['vertices']==vv and nodes[ch]['mass']==ratio*n['mass']
 assert visited==set(range(len(nodes)))
 leaves=[n for n in nodes if n['status']!='split'];assert sum(n['mass'] for n in leaves)==1
 summary={'scope':'bounded exact covering tree with OPEN leaves; NOT global','processed':processed,'counts':{s:sum(n['status']==s for n in nodes) for s in ['split','certified','open']},'certified_mass':str(sum(n['mass'] for n in leaves if n['status']=='certified')),'seconds':time.time()-started}
 out={'summary':summary,'fields':fields,'nodes':[{**n,'mass':str(n['mass']),'vertices':[[str(x) for x in y] for y in n['vertices']]} for n in nodes]}
 (P/'cosine_tree_pilot.json').write_text(json.dumps(out,indent=2));print(summary,flush=True)
if __name__=='__main__':main()
