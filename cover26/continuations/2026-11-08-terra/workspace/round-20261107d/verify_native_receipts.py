"""Rehash restored historical reports without promoting their historical claims."""
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def demand(p,message):
    if not p:raise ValueError(message)

expected='ba52dbb56f9d273c30e1b356c55bdb0d3ff8fdaa36061248e5c8ec1e490a81a1'
current_path=HERE/'native-recovered/n26-mixed-after-six-midarc-supplemental-current-v1.json'
final_path=ROOT/'audit/native-recovered/cover26/proof_bundle/outputs/n26-mixed-after-six-midarc-independent-final-v1.json'
demand(sha(current_path)==expected,'restored formal current bytes')
demand(sha(final_path)=='6099c25ff78f074c5a02dd90c33c2d3f481df350ea71b2e853ca9fc2deeabbbc','formal independent final bytes')
current=json.loads(current_path.read_text());final=json.loads(final_path.read_text())
demand(final['current_audit_sha256']==expected,'same original report pair')
demand(current['candidate_angle_unresolved_closed_boxes']==16 and current['Rstar_conditional_frontier_pending_subtrees']==4957,'formal frontier unchanged')
demand(len(current['files'])==273731 and final['current_file_digests_rechecked']==273731,'historical inventory cardinality')
for key in ['unrestricted_reduction_final_joint_acceptance','full_catalog_complete','global_lower_bound_proved','global_optimality_proved']:
    demand(current[key] is False and final[key] is False,'historical unresolved scope')
sources=[]
for path in sorted((HERE/'native-source').glob('SOURCE-MANIFEST*.json')):
    for row in json.loads(path.read_text()):
        source=HERE/'native-source'/row['local'];raw=source.read_bytes()
        git=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        demand(git==row['blob_sha'],'public source bytes: '+row['local'])
        sources.append({**row,'bytes':len(raw),'sha256':sha(source)})
targets={
    'e555cb470ef4a3a8c5167f95307e7b0220c8b77a0fe7b435010220450eb44ef7',
    '598d65cbc3d839780e3f6b8dbdc3cd36331a391f716eacc1cae83144903b2794',
}
target_refs=[{'path':p,'sha256':h} for p,h in current['files'].items() if h in targets]
result={'passed':True,'restored_current_sha256':expected,'paired_final_sha256':sha(final_path),
    'historical_formal_roots':16,'historical_conditional_prefixes':4957,
    'historical_inventory_entries':273731,'original_system_and_root_certificate_references':target_refs,
    'public_sources':sources,'all_273731_original_dependency_bytes_replayed_now':False,
    'mathematical_frontier_payments':0,'global_optimality_proved':False}
(HERE/'NATIVE-RECEIPTS.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('PASS original current/final byte identities and',len(sources),'public sources; no full semantic replay')
