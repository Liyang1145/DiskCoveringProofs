"""Independent scalar rational clipping and sourcebound leafreplay on C1333 tightdomain."""
from q10_rational_polytope_audit import *
from q11_chord_flow_fraction_replay import replay
if __name__=='__main__':
 src=P/'q10-c1334-slab-controls.json';raw=src.read_bytes();a=json.loads(raw);base=json.loads((P/'q10-c1334-domain.json').read_text());assert base['source_sha256']==hashlib.sha256((P/'q10-tight-metric-domain.json').read_bytes()).hexdigest();assert base['audit_sha256']==hashlib.sha256((P/'q10-tight-slab-audit.json').read_bytes()).hexdigest();V,cs=decode(base['polytope']);out=[];faces=json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][879]['faces']
 for row in a['runs']:
  if not row['replay']['excluded']:continue
  VV,cc=decode(row['polytope']);assert cc[:-1]==cs;n,r=cc[-1];assert n==tuple(Q(row['side'])*int(i in row['indices'])for i in range(10))and r==Q(row['side'])*Q(row['threshold_total_fraction']);expected,_=clip(V,cs,n,r);assert VV==expected;c=row['certificate'];assert c['index']==879 and c['flow']['faces']==faces and {tuple(scalar(t)for t in v)for v in c['polytope']['vertices']}==VV;rr=replay(c);assert rr['excluded'];out.append({'indices':row['indices'],'side':row['side'],'threshold':row['threshold_total_fraction'],'vertices':len(VV),'replay':rr});print('TIGHTAUDIT',row['indices'],row['side'],len(VV),flush=True)
 cuts=set();autos=json.loads((P/'q10-fan-transport.json').read_text())['runs']
 for row in out:
  for g in autos:
   dg={int(k):v for k,v in g['deficit_permutation'].items()};cuts.add((tuple(sorted(dg[i]for i in row['indices'])),-row['side'],row['threshold']))
 report={'status':'sourcebound_rational_clip_leaf_exclusions_and_finite_transport','source_sha256':hashlib.sha256(raw).hexdigest(),'base_sha256':hashlib.sha256((P/'q10-c1334-domain.json').read_bytes()).hexdigest(),'runs':out,'cuts':[{'indices':list(ids),'sense':'greater'if s==1 else'less','fraction_of_total':t}for ids,s,t in sorted(cuts)]};(P/'q10-c1334-slab-audit.json').write_text(json.dumps(report,indent=2));print(report['cuts'],flush=True)

