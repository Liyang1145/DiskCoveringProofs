"""Try eliminate actualr onQ0 via positive derivative and nested widthdomains."""
import patch_ridge_jet as j
import interval_joint_patch as k
import json,math
from pathlib import Path
lo=k.lf(k.g);hi=k.uf(2*k.asin(k.R));cuts=[lo+(hi-lo)*i/24 for i in range(25)];cuts[0]=lo;cuts[-1]=hi
minimum=math.inf;maximum=-math.inf;unsafe=0
for a,b in zip(cuts,cuts[1:]):
 for c,d in zip(cuts,cuts[1:]):
  box=[k.I('.379','.38'),k.I('1.106','1.108'),k.I('1.068','1.071'),k.I(0),k.I(a,b),k.I(c,d),k.I(0)]
  try:
   v=j.objective(box).d[0];minimum=min(minimum,k.lf(v));maximum=max(maximum,k.uf(v))
  except j.Unsafe:unsafe+=1
out={'scope':'ridgeQ0 andfullwidthsquare[g,2asinR0] analyticextension','derivative_r_lower':minimum,'derivative_r_upper':maximum,'unsafe':unsafe,'subboxes':576,'positive':minimum>0 and unsafe==0};Path(__file__).with_name('ridge_r_derivative.json').write_text(json.dumps(out,indent=2));print(out)
