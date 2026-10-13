"""Exact rational controls for geometric near-pi band containment."""
from fractions import Fraction as F
from pathlib import Path
import json
P=Path(__file__).parent;eps=F(1,10**8);U=F(37999,100000);R0=F(19,50)
assert U**2<F(4,25)
assert 8*eps<F(3,10000)**2
assert 8*eps/F(3,8)<F(3,10000000)
loss=F(3,10000)+F(3,10000000);assert loss==F(3003,10000000)
margin=F(3,8)-loss-R0*F(493,500);assert margin==F(197,10000000)>0
out={'epsilon':str(eps),'radius_loss_bound':str(loss),'normalized_lower':'493/500','exact_margin':str(margin),'scope':'rational inequalities only; geometric crossproduct and norm derivation in ENDPOINT-ANGLE-GAP.md; h>1/50 from prior directed chord control'}
(P/'endpoint_angle_gap_control.json').write_text(json.dumps(out,indent=2));print(out)
