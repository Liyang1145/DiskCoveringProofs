"""255 processed DBM cells, exact pair-midpoint coverage. No global conclusion if open.
Calibration central simplex and node26 domain enlargement, exact DBM empty-cell control.
"""
from certify_cosine_polytope import *
import time

def root_angles():
 cert=json.loads((P/'repaired_tc_krawczyk.json').read_text())['certificate'];rr=F(float.fromhex(cert['radius_hex']))
 z=[I(F(float.fromhex(x)))+iv.mpf([-hi(I(rr)),hi(I(rr))]) for x in cert['center_hex']][:7]
 a=[z[0],z[1],z[2],z[3],iv.pi-2*sum(z[:4]),z[3],z[2],z[1],z[0]];th=[iv.mpf(0) for _ in range(9)]
 for k in range(5,9):th[k]=th[k-1]+a[k-1]+a[k]
 for k in range(3,-1,-1):th[k]=th[k+1]-a[k]-a[k+1]
 raw=[th[k]+a[k] for k in range(9)]
 return [iv.mpf(0)]+[raw[(i+2)%9]-raw[2]+(2*iv.pi if i>=7 else 0) for i in range(1,9)]
ROOT_ANGLES=root_angles()

def known_patch(db):
 lower=[-db[i+1][i] for i in range(9)];upper=[db[i][i+1] for i in range(9)]
 if min(lower)>=F(31,450):return 'C913'
 for j in range(9):
  t=F(3,5) if j in [0,1,2,5,6] else F(13,20) if j in [4,7] else F(3,4)
  if lower[j]>=t:return 'C914-corner'+str(j)
 p=json.loads((P/'canonical_local_patch_certificate.json').read_text());c=[F(x) for x in p['center_y']];e=F(p['halfwidth_independent8'])
 if all(lower[i]>=c[i]-e and upper[i]<=c[i]+e for i in range(8)):return 'C916'
 if all(lower[(2-i)%9]>=c[i]-e and upper[(2-i)%9]<=c[i]+e for i in range(8)):return 'C916-reflected'
 # Direct C915 chart containment avoids the narrower rational independent-y cube.
 roots=ROOT_ANGLES # Recomputed from exact dyadic C891 box, not serialized decimal endpoints.
 q2=iv.mpf(0)
 for k in range(8):
  i=(k-2)%9
  # db[6][i] bounds t_i-t_6; opposite bound gives lower endpoint.
  tt=iv.mpf([lo(I(-db[i][6])),hi(I(db[6][i]))])
  h=(i-6)*L-D*tt-(roots[i]-roots[6])
  q2+=h**2
 if q2<=I(F(431,10**6))**2:return 'C915-direct-DBM'
 if q2<=I(F(3,2000))**2:return 'C918-direct-DBM'
 if q2<=I(F(191,25000))**2:return 'C919-direct-DBM'
 if q2<=I(F(729,50000))**2:return 'C920-direct-DBM'
 # Reflection rho(y)_j=y_(2-j): sum of a cyclic block remains a cyclic block.
 def subset_bounds(inds):
  if not inds:return F(0),F(0)
  inds=sorted(inds)
  if inds==list(range(inds[0],inds[-1]+1)):
   a,b=inds[0],inds[-1]+1;return -db[b][a],db[a][b]
  comp=sorted(set(range(9))-set(inds));assert comp==list(range(comp[0],comp[-1]+1))
  a,b=comp[0],comp[-1]+1;return 1-db[a][b],1+db[b][a]
 rq2=iv.mpf(0)
 for k in range(8):
  i=(k-2)%9;l,u=subset_bounds([(2-j)%9 for j in range(min(i,6),max(i,6))])
  if i<6:l,u=-u,-l
  tt=iv.mpf([lo(I(l)),hi(I(u))]);h=(i-6)*L-D*tt-(roots[i]-roots[6]);rq2+=h**2
 if rq2<=I(F(191,25000))**2:return 'C919-reflected-DBM'
 if rq2<=I(F(729,50000))**2:return 'C920-reflected-DBM'
 return None

def main():
 import sys
 resume='--resume' in sys.argv;budget=2047 if resume else 255
 fields=json.loads((P/'energy_library.json').read_text())['fields'];extra=json.loads((P/'cosine_gap_diagnostic.json').read_text())['rows'];fields+= [r['new_field'] for r in extra]
 rt=rootdbm();assert rt[0][9]==1 and rt[9][0]==-1
 bad=[r[:] for r in rt];bad[0][9]=F(1,2);assert closure(bad) is None
 center=[r[:] for r in rt]
 for i in range(9):center[i+1][i]=-F(31,450)
 center=closure(center);cr=solve(center,fields);cc=certify(center,cr,fields);assert cc['certified_gt_19_50']
 # Single-cell angular width zero stress yields no negative sign surprise; full graph normalized energy positive.
 nodes=[{'id':0,'db':rt,'status':'open','depth':0}]
 if resume:
  nodes=json.loads((P/'cosine_dbm_pilot.json').read_text())['nodes']
  for n in nodes:n['db']=[[F(x) for x in row] for row in n['db']]
 queue=deque(n['id'] for n in nodes if n['status']=='open');start=time.time();processed=0
 while queue and processed<budget:
  idx=queue.popleft();n=nodes[idx];processed+=1;pp=known_patch(n['db'])
  if pp:n.update({'status':'certified','patch':pp});continue
  r=solve(n['db'],fields);n['numeric_lower']=r['radius_lower_numeric']
  if r['radius_lower_numeric']>.380001:
   cert=certify(n['db'],r,fields)
   if cert['certified_gt_19_50']:n.update({'status':'certified','certificate':cert});continue
  pair=r['branch_pair'];mid,a,b=branches(n['db'],pair);n.update({'status':'split','pair':pair,'midpoint':str(mid),'children':[]})
  for db in [a,b]:
   if db is None:raise AssertionError('midpoint of closed nonzero interval should yield feasible children')
   ni=len(nodes);n['children'].append(ni);nodes.append({'id':ni,'db':db,'status':'open','depth':n['depth']+1});queue.append(ni)
  if processed%50==0:print('processed',processed,'certified',sum(n['status']=='certified' for n in nodes),'open',len(queue),flush=True)
 # Exact replay all child constraints; coverage follows dichotomy s<=mid or s>=mid, closure equivalent.
 visited={0}
 for n in nodes:
  if n['status']!='split':continue
  mid,a,b=branches(n['db'],n['pair']);assert str(mid)==n['midpoint'] and len(n['children'])==2
  for ch,db in zip(n['children'],[a,b]):assert ch not in visited and nodes[ch]['db']==db;visited.add(ch)
 assert visited==set(range(len(nodes)))
 summary={'scope':'fixed51edge oracle, pairDBM partition; OPEN leaves retained; NOT global','counts':{s:sum(n['status']==s for n in nodes) for s in ['split','certified','open']},'processed':processed,'seconds':time.time()-start}
 (P/('cosine_dbm_extension.json' if resume else 'cosine_dbm_pilot.json')).write_text(json.dumps({'summary':summary,'calibration_central':cc,'fields':fields,'nodes':[{**n,'db':[[str(x) for x in row] for row in n['db']]} for n in nodes]},indent=2));print(summary,flush=True)
if __name__=='__main__':main()
