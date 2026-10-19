import json,time
from fractions import Fraction as F
import numpy as np
import certify_box as cb
R={r['index']:r for r in json.load(open('diag_merged.json'))}
d=json.load(open('dl/root25-slim.json'))
B={b['index']:b for b in d['pending_closed_leaf_boxes']}
i=int(__import__('sys').argv[1])
lo=[F(x) for x in B[i]['lower']]; hi=[F(x) for x in B[i]['upper']]
th=np.array(R[i]['None'][1])
t=time.time(); lam,s=cb.fit_weights(th); print('fit s',s**0.5-0.2347000904, time.time()-t)
wq=cb.rationalize_weights(lam)
t=time.time(); pairs,W=cb.exact_pairs(wq); print('exact kernel',time.time()-t,len(pairs))
t=time.time(); b,st=cb.box_bound(pairs,W,lo,hi); print('whole box bound/W',float(b/W) if b is not None else st, time.time()-t)
