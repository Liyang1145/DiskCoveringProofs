from certify_cosine_polytope import *
from cosine_dbm_pilot import known_patch
import numpy as np

def main():
 d=json.loads((P/'cosine_dbm_mirror.json').read_text());c=np.array([float(F(x)) for x in json.loads((P/'canonical_local_patch_certificate.json').read_text())['center_y']]);rows=[]
 for n in d['nodes']:
  if n['status']!='open':continue
  db=[[F(x) for x in r] for r in n['db']];r=solve(db,d['fields']);low=np.array([float(-db[i+1][i]) for i in range(9)]);up=np.array([float(db[i][i+1]) for i in range(9)]);y=np.array(r['y_numeric']);row={'node':n['id'],'depth':n['depth'],'lower_numeric':r['radius_lower_numeric'],'y_numeric':y.tolist(),'max_y_width':float(max(up-low)),'distance_to_root_numeric':float(np.linalg.norm(y-c)),'root_center_in_cell':all(sum(F(str(c[k])) for k in range(i,j))<=db[i][j] and sum(F(str(c[k])) for k in range(i,j))>=-db[j][i] for i in range(10) for j in range(i+1,10)),'branch_pair':r['branch_pair'],'pair_gap':r['largest_pair_gap'],'known_patch':known_patch(db)};rows.append(row)
 (P/'remaining_dbm_diagnostic.json').write_text(json.dumps(rows,indent=2));print([{k:v for k,v in r.items() if k!='y_numeric'} for r in rows])
if __name__=='__main__':main()
