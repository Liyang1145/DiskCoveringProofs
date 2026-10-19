import json,time,os
import diag_open as m
done=set(json.loads(l)['index'] for fn in os.listdir('diag') if fn.endswith('.jsonl') for l in open('diag/'+fn))
for f in os.listdir('diag'):
  if f.startswith('d_'): done|={r['index'] for r in json.load(open('diag/'+f))}
todo=[i for i,b in enumerate(m.boxes) if b['index'] not in done]
print(len(todo),todo[:6],flush=True)
import numpy as np
from fractions import Fraction as F
i=todo[0]; b=m.boxes[i]; lo=np.array([float(F(x)) for x in b['lower']]); hi=np.array([float(F(x)) for x in b['upper']])
for owner in (None,16,25):
  t=time.time(); r=m.solve(lo,hi,owner,(lo+hi)/2); print(owner, time.time()-t, r[0]-m.RS, r[1], flush=True)
