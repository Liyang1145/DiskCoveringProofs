"""High-precision proposal generator; exact acceptance is a separate program."""
from pathlib import Path
import json
import sympy as sp
import mpmath as mp
from candidate_model import build,NAMES,TRIANGLES

HERE=Path(__file__).resolve().parent
mp.mp.dps=125
Z,F=build();J=F.jacobian(Z)
fun=sp.lambdify([Z],F,'mpmath',cse=True)
jac=sp.lambdify([Z],J,'mpmath',cse=True)
proposal=json.loads((HERE/'stationary-proposal.json').read_text())
seed=[mp.mpf(str(x)) for x in proposal['coordinates']+proposal['multipliers']]
root=mp.findroot(lambda *x:fun(x),seed,J=lambda *x:jac(x),tol=mp.mpf('1e-115'),maxsteps=30)
center=[mp.nstr(x,105) for x in root]
inverse=mp.inverse(jac(root))
out={'coordinate_names':NAMES,'dimension':26,'triangles':TRIANGLES,
     'center':center,'inverse_jacobian':[[mp.nstr(inverse[i,j],105) for j in range(26)] for i in range(26)],
     'box_half_width':'1e-75','note':'Proposals only; require verify_root.py before treating as an isolated root.'}
(HERE/'root-proposal.json').write_text(json.dumps(out,indent=2)+'\n')
print('radius',mp.nstr(root[13],110))
print('max residual',mp.nstr(max(abs(x) for x in fun(root)),8))
print('inverse infinity norm',mp.nstr(max(sum(abs(inverse[i,j]) for j in range(26)) for i in range(26)),12))
