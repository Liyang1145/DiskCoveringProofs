"""Four bounded jointlocal starts test whether partitionloss hides different lowradius basin; notglobalproof."""
from anchor_outer_local_probe import run,P,json
if __name__=='__main__':
 a=json.loads((P/'q10-polytope-partition-879.json').read_text());ss=[n for n in a['nodes']if n.get('status')=='split'];chosen=[ss[0],a['nodes'][51],ss[len(ss)//2],ss[-1]];out=[]
 for n in chosen:
  r=run(n['flow_proposal']);r['source_node']=n['id'];out.append(r)
 (P/'q10-joint-basin-control.json').write_text(json.dumps({'status':'numeric_only_four_localstarts','runs':out},indent=2))
