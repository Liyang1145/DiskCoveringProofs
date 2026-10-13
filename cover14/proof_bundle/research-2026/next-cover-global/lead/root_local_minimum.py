"""Rigorous local min on the TWO-CONTACT D2 curve only, not arbitrary configurations."""
import json
from pathlib import Path
from root_integer_certificate import I,J,Q,S,expr
P=Path(__file__).resolve().parent
cert=json.loads((P/'root-integer-certificate.json').read_text());X=[I(int(Q(a)*S),int(Q(b)*S),True)for a,b in cert['box_dyadic']]
F,G=expr(*(J.var(x,i)for i,x in enumerate(X)))
# J_{(c,r)} invertible -> c(z),r(z) locally. At H=0, r'=0.
D=F.g[1]*G.g[2]-F.g[2]*G.g[1];assert D.lo*D.hi>0
cp=-F.g[0]/F.g[1];v=[I(1),cp,I(0)]
QF=sum((v[i]*F.h[i][j]*v[j]for i in range(3)for j in range(3)),I(0));QG=sum((v[i]*G.h[i][j]*v[j]for i in range(3)for j in range(3)),I(0))
rpp=(G.g[1]*QF-F.g[1]*QG)/D
assert rpp.lo>0
out={'status':'certified_local_minimum_D2_contact_curve','scope':'strict local minimum of r along original F=G=0 selected positive radical D2 branch only; NOT all D2 covers or all14-center covers','det_FG_c_r':D.dec(),'dc_dz_at_stationary':cp.dec(),'d2r_dz2_at_stationary':rpp.dec(),'proof':'IFT from nonzero det(FG_c,r); H=0 implies dr/dz=0. Twice differentiating F=G=0 gives displayed rpp; interval lower>0 proves strict local minimum on this curve.'}
(P/'root-local-minimum.json').write_text(json.dumps(out,indent=2));print('d2r/dz2 enclosure',[float(Q(t))for t in rpp.dec()]);print('det_FG_c_r',[float(Q(t))for t in D.dec()])
