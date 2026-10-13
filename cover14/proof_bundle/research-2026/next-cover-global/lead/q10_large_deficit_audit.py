"""Independent complete scalarclipping and Fraction replay of successful large-deficit slabs."""
from q10_rational_polytope_audit import *
from q11_chord_flow_fraction_replay import replay
if __name__=='__main__':
 src=P/'q10-large-deficit-controls.json';raw=src.read_bytes();a=json.loads(raw);base=P/'q10-c1341-domain.json';V,cs=decode(json.loads(base.read_text())['polytope']);out=[];cuts=set();autos=json.loads((P/'q10-fan-transport.json').read_text())['runs']
 for row in a['runs']:
  if not row['replay']['excluded']:continue
  VV,cc=decode(row['polytope']);assert cc[:-1]==cs;n,r=cc[-1];assert n==tuple(Q(row['side'])*int(i in row['indices'])for i in range(10))and r==Q(row['side'])*Q(row['threshold_total_fraction']);expected,_=clip(V,cs,n,r);assert VV==expected;c=row['certificate'];assert c['index']==879 and {tuple(scalar(t)for t in v)for v in c['polytope']['vertices']}==VV;rr=replay(c);assert rr['excluded'];out.append({'indices':row['indices'],'side':row['side'],'threshold':row['threshold_total_fraction'],'vertices':len(VV),'replay':rr})
  for g in autos:
   dg={int(k):v for k,v in g['deficit_permutation'].items()};cuts.add((tuple(sorted(dg[i]for i in row['indices'])),-row['side'],row['threshold_total_fraction']))
  print('LARGEAUDIT',row['indices'],row['side'],len(VV),flush=True)
 report={'status':'sourcebound_rational_clip_leaf_exclusions_and_finite_transport','source_sha256':hashlib.sha256(raw).hexdigest(),'base_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'runs':out,'cuts':[{'indices':list(ids),'sense':'greater'if s==1 else'less','fraction_of_total':t}for ids,s,t in sorted(cuts)]};(P/'q10-large-deficit-audit.json').write_text(json.dumps(report,indent=2));print(report['cuts'],flush=True)
