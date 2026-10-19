"""Re-verify every root25 OPEN-box certificate with verify_certs.py (fresh subprocess
per file, 2 in parallel) and write ROOT25-FOREST-INDEX.json (atomic)."""
import json, os, hashlib, subprocess, sys
from multiprocessing import Pool
ROOT='/workspace/work/dcp-n26'
P=[b['index'] for b in json.load(open(ROOT+'/pending.json'))['pending_closed_leaf_boxes']]
def one(i):
    path=ROOT+'/certs/%d.json'%i
    if not os.path.exists(path): return {'index':i,'status':'NO-CERT'}
    h=hashlib.sha256(open(path,'rb').read()).hexdigest()
    r=subprocess.run(['python3',ROOT+'/verify_certs.py',path],capture_output=True,text=True)
    try: v=json.loads(r.stdout.strip().splitlines()[-1])
    except Exception: v={'error':r.stderr[-300:]}
    st='CLOSED-ENERGY' if v.get('CLOSED') else ('CLOSED-ENERGY+LOCAL-CARVEOUT' if v.get('CLOSED_WITH_LOCAL_CARVEOUT') else 'OPEN')
    return {'index':i,'cert':'certs/%d.json'%i,'sha256':h,'status':st,'energy_leaves':v.get('leaves'),'local_leaves':v.get('local',0),
            'open_leaves':v.get('open'),'failed_leaves':v.get('fail'),'min_margin_over_W':v.get('min_margin_over_W'),'verify':v}
if __name__=='__main__':
    with Pool(2) as p: rows=sorted(p.map(one,P,chunksize=1),key=lambda r:r['index'])
    from collections import Counter
    cnt=Counter(r['status'] for r in rows)
    mm=min((r['min_margin_over_W'] for r in rows if r.get('min_margin_over_W') is not None and r['status']!='OPEN'),default=None)
    out={'schema':'root25-fresh-arithmetic-forest-index-v1',
         'source':'root25 OPEN boxes of cover26 composition sha256 c1675552b56d762de0bca83ca3adbb28e06c71e95c94b387d7f216eee41187c9 (pending.json)',
         'model':'model134.json (134-rod edge list reconstructed from committed kernels; not checked against SYSTEM.json)',
         'checker':'verify_certs.py sha256 '+hashlib.sha256(open(ROOT+'/verify_certs.py','rb').read()).hexdigest(),
         'counts':dict(cnt),'total_boxes':len(rows),
         'total_energy_leaves':sum(r.get('energy_leaves') or 0 for r in rows if r['status']!='OPEN'),
         'min_margin_over_W_closed':mm,'boxes':rows,
         'scope':'arithmetic inside the archive 134-rod energy model only; not a formal geometry payment; n=26 NOT proved'}
    tmp=ROOT+'/.forest.tmp'; json.dump(out,open(tmp,'w'),indent=0); os.replace(tmp,ROOT+'/ROOT25-FOREST-INDEX.json')
    print(json.dumps({k:out[k] for k in ['counts','total_boxes','total_energy_leaves','min_margin_over_W_closed']}))
