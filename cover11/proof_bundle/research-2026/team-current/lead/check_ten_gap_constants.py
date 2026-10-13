"""Exact rational / interval controls for TEN-DISK-GAP-COMPACTNESS (not graph certificate)."""
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp,json
mp.iv.dps=40;I=mp.iv.mpf;P=Path(__file__).parent
s=F(19,50);U=F(37999,100000);delta=2*(s-U)
assert delta==F(1,50000) and delta/(2*U)==F(1,37999)
# Exact positivity of 8asin(19/50)<pi via sin(pi/8)^2=(2-sqrt2)/4.
# 2-4s²>0 and its square>2.
z=2-4*s*s;assert z>0 and z*z>2
# Analytic center norm bounds, switch cosb>=R/2>=3/16.
# Width gap at U rigorously positive via interval asin=atan2(U,sqrt(1-U²)).
r=I(U.numerator)/U.denominator;asin=mp.iv.atan2(r,mp.iv.sqrt(1-r*r));gap=2*mp.iv.pi-16*asin
assert gap.a>0
# Chord>=2sin(gap/2)>0.04; direct interval control.
ch=2*mp.iv.sin(gap/2);assert ch.a>I('0.04')
out={'scope':'exact rational constants and40dps interval gap only; analytic proof in TEN-DISK-GAP-COMPACTNESS.md','s':str(s),'U':str(U),'delta':str(delta),'sine_lower':str(delta/(2*U)),'eight_arcs_square_margin':str(z*z-2),'width_gap':str(gap),'chord_lower':str(ch),'switch_cos_lower':'3/16'}
(P/'ten_gap_constants_control.json').write_text(json.dumps(out,indent=2));print(out)
