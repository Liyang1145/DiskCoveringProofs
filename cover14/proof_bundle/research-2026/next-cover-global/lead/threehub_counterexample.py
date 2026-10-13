"""Exact control: three disks covering core do NOT force each hub norm<=U."""
from root_integer_certificate import I,Q,S
import json
from pathlib import Path
P=Path(__file__).resolve().parent
U=I('0.33173203427623414');a=1-2*U
# Rational sites; allnorms<1-U; firstnorm.4>U.
h=[(I('0.4'),I(0)),(I('-0.1'),I('0.2')),(I('-0.1'),I('-0.2'))]
# Only interiorVoronoivertex (.11,0) hasradius .29.
assert (U*U-I('.29')**2).lo>0
# boundary Voronoiswitches: y=0 negative-axis, and .5x-.2y=.055.
# Circle-line intersections x=(k A +/- B sqrt((A²+B²)a²-k²))/(A²+B²).
A=I('.5');B=I('-.2');k=I('.055');ss=A*A+B*B;v=(ss*a*a-k*k).sqrt()
xs=[(k*A+B*v)/ss,(k*A-B*v)/ss]
# upper switch uses largex, ypositive; smallx islower crossingnotnearesttoh2.
x=xs[1];y=(k-A*x)/B
assert x.lo>0 and y.lo>0
rad2=a*a+I('.16')-I('.8')*x
negative_axis=(a-I('.1'))**2+I('.04')
# Oncircleownedarcs maximumdistance occursatanendpoint oranti-center direction.
# Theh1ownedarc aboutangle0 excludesantipodalanglepi; h2/h3 likewise nearestbisectors.
# Moredirect allcirclecirclecovered: boundary cap halfwidth pair overlaps can be checkeddot signs, but here use Voronoipieces.
assert (U*U-rad2).lo>0 and (U*U-negative_axis).lo>0
# H2/H3 radial antipodes lieonright-half, whereh1iscloser; for h2 antipode ynegative makes h3closer; analogh3.
assert (I('.4')-U).lo>0
out={'status':'exact_counterexample_to_hub_norm_inference','centers':[['2/5','0'],['-1/10','1/5'],['-1/10','-1/5']],'core_radius':'1-2U','disk_radius_U':'0.33173203427623414','interior_vertex':['11/100','0'],'interior_radius':'29/100','boundary_switch_sqrad_interval':rad2.dec(),'negative_axis_sqrad_interval':negative_axis.dec(),'scope':'3diskcoverofcore withonecenter norm>U; NOT14diskcovercounterexample'}
(P/'threehub-counterexample.json').write_text(json.dumps(out,indent=2));print('counterexample verified: norms .4,.2236,.2236, maxcore radius< U')
