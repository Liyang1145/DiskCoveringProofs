import sys,json
from fractions import Fraction as F
sys.path.insert(0,'/workspace/work/dcp-n26/repo/cover26/proof_bundle/outputs/n26-sharp-candidate-angles-published-replay-v1')
from n26_force import load_trig
from n26_direct_arc_force import force_check
RUP=F("0.234700090400448239616790133776692127560495963654971391785925")
P=json.load(open('/workspace/work/dcp-n26/repo/cover26/proof_bundle/work/n26-sharp-candidate-angles-proposal-v3.json'))
spec=P['spec'];nodes=P['nodes'];arcs=load_trig()[0]
B=json.load(open('boxes.json'))['boxes']
T=[97,98,99,100,135,136,175,176,289,290,296,308,295,304]
for t in T:
  lo=[F(x) for x in B[str(t)]['lo']];hi=[F(x) for x in B[str(t)]['hi']]
  best=None
  for i,n in enumerate(nodes):
    if n['kind']!='FORCE':continue
    m=F(force_check(spec,lo,hi,n['cert'],arcs)['required_radius_lower'])-RUP
    if best is None or m>best[0]: best=(m,i)
  print(t,float(best[0]),best[1],flush=True)
