"""Exact consequences of saved interval Hessian + capgradient, with root-anchor comparison."""
import json,hashlib
from fractions import Fraction as F
from pathlib import Path
from root_integer_certificate import I,S,calibrate
from shared_radius_corner_fraction_kernel import sc
import q11_chord_flow_fraction_replay as fr
P=Path(__file__).resolve().parent;calibrate();a=json.loads((P/'q10-adaptive-flow-interval.json').read_text());assert a['status']=='certified_hessian'and F(a['row_bound'])<1
audit=json.loads((P/'q10-adaptive-flow-fraction-audit.json').read_text());assert audit['source_sha256']==hashlib.sha256((P/'q10-adaptive-flow-interval.json').read_bytes()).hexdigest() and F(audit['row_bound'])<1
th=list(map(F,a['theta0']));eps=F(a['epsilon']);kap=F(a['kappa']);q=F('.03374975397719135');target=[-q,0,0,0,q,-q,0,0,0,q];err=sum(max(abs(F(lo)-v),abs(F(hi)-v))for (lo,hi),v in zip(a['gradient'],target))
capbase=th[5]-th[4]+th[0]-th[9];caplower=capbase+2*fr.pi[0]-2*fr.L[1]
loss=-F(a['f0'][0])-q*caplower+eps*err;rad2=2*loss/kap
root=json.loads((P/'root-integer-certificate.json').read_text());z,c,r=[I(int(F(lo)*S),int(F(hi)*S),True)for lo,hi in root['box_dyadic']];s=(1-r*r).sqrt();aa=(s+z)/2;bb=r+(r*r-(aa-z)**2).sqrt();dd=1-(r*r-c*c).sqrt();v1=(1+aa*aa+bb*bb-r*r)/2;v2=(1+c*c+dd*dd-r*r)/2;det=aa*dd-bb*c;px=(v1*dd-v2*bb)/det;py=(aa*v2-c*v1)/det
A=[(s,r),(px,py),(I(0),I(1)),(-px,py),(-s,r),(-s,-r),(-px,-py),(I(0),I(-1)),(px,-py),(s,-r)]
maxerr=F(0)
for t,pp in zip(th,A):
 sn,cs=sc(abs(t));sn=(-sn[1],-sn[0])if t<0 else sn
 err2=F(0)
 for rr,iv in zip(pp,[cs,sn]):
  lo=F(rr.lo,S)-iv[1];hi=F(rr.hi,S)-iv[0];err2+=max(abs(lo),abs(hi))**2
 maxerr=max(maxerr,err2)
# unit circle points chord<=1e-14 => aligned angularerror<=2e-14 (coshalf>=1/2).
assert maxerr<F(1,10**14)**2
assert 0<rad2<F(1,10**6)**2
out=dict(status='exact_consequence_conditional_saved_Hessian',epsilon=str(eps),gradient_l1_residual=str(err),capgradient_lower=str(q*caplower),loss=str(loss),radius_squared=str(rad2),radius_upper='1/1000000',reference_anchor_error_squared=str(maxerr),reference_angle_error='1/50000000000000',scope='For saved rationalreference: full literal879 14site/16face/10orderedunitcircleanchor witnessconfiguration at r<=U, with cyclicgaps<=L and mean-gauged theta-th0 sumzero and supnorm<=eps, has Euclidean angleerror<1e-6; supnorm<=Euclideannorm and referenceangleerror<2e-14 imply2e-6truecandidatecell aftersamecommonrotation, C1355 applies. Not claimedfor40edgecorealone.')
(P/'q10-adaptive-local-bridge.json').write_text(json.dumps(out,indent=2));print({k:float(F(out[k]))for k in['epsilon','gradient_l1_residual','capgradient_lower','loss','radius_squared']})
