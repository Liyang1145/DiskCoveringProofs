import json,numpy as np
from pathlib import Path
p=Path('research-2026/team-current/lead');s=(p/'shared_moment_dual.py').read_text();s=s[:s.index(' K=len(factors)')]+'''
 z=np.array(json.loads((P/f'shared_moment_dual_{start}_{span}.json').read_text())['z'])
 cert=json.loads((P/f'shared_moment_certificate_{start}_{span}.partial.json').read_text())
 for q,(v,M) in zip(cert,factors):
  f=float(np.max(v+M@z));print(q['factor'],round(f,7),round(q['upper']-f,7))
'''
import sys;sys.argv=['x','2','4'];exec(compile(s,str(p/'shared_moment_dual.py'),'exec'))
