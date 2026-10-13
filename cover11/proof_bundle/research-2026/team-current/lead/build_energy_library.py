"""Exact positive scalar stress library from saved vector-force proposals.
Each stored field verified by exact Schur algebra. Zero/negative or numerical optimizer weights not used directly.
"""
from certify_energy_cell import schur
from simplex_tree_pilot import *
import time

def main():
 d=json.loads((P/'adaptive_stellar_pilot.json').read_text());old=json.loads((P/'energy_cell_certificate.json').read_text());cache={f['name']:f for f in old['fields']};out=[];start=time.time()
 for f in d['fields']:
  if f['name'] in cache:out.append(cache[f['name']]);continue
  ff=schur(f['forces'],f['name']);out.append({**ff,'weights':[(i,j,str(w)) for i,j,w in ff['weights']]})
  (P/'energy_library.json').write_text(json.dumps({'scope':'exact rational normalized positive scalar fields; no global cell conclusion','fields':out},indent=2))
 print('fields',len(out),'seconds',time.time()-start)
if __name__=='__main__':main()
