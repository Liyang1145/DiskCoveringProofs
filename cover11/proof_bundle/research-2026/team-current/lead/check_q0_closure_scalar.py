"""Separate scalar dual assembly at saved coordinate candidate: numerical interface calibration."""
from pathlib import Path
import numpy as np,json,math
P=Path(__file__).parent;exec((P/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0])
reports=[]
for stem,rrr in [('q0_closure_dual',.38),('q0_lower375_dual',.375)]:
 J=json.loads((P/f'{stem}_0_4.json').read_text());z=np.array([float(f'{v:.9f}') for v in J['z']]);assert J['faces']==faces and J['edges']==[list(e) for e in edges]
 aa=x0[:33].reshape(11,3);bs=x0[33:42];ys=np.exp(x0[42:62]+x0[-1])/rrr;als,ws,cls,area=calc(x0)
 const=pi*(sum(z[:9])+2*sum(z[9:11])+sum(z[50:71])-2*z[71])-pi*sum(z[112:]);D=const
 for t,f in enumerate(faces):
  D+=2*rrr**2*ys[t]**2*np.prod(np.sin(aa[t]))
  for k,i in enumerate(f):
   e=tuple(sorted(j for j in f if j!=i));ei=edges.index(e);adj=[tt for tt,ff in enumerate(faces) if set(e)<=set(ff)];sg=1 if adj[0]==t else -1
   D+=-(z[i]+z[50+ei])*aa[t,k]+sg*z[11+ei]*ys[t]**2*math.sin(aa[t,k])**2+sg*z[73+ei]*ys[t]*math.sin(aa[t,k])
 for i in range(9):
  j=(i+1)%9;ei=edges.index(tuple(sorted((i,j))));b=bs[i];y=ys[11+i]
  D+=rrr**2*y*y*math.sin(2*b)/2+(z[i]+z[j]-z[50+ei]+2*z[112+i])*b-z[11+ei]*y*y*math.sin(b)**2-z[73+ei]*y*math.sin(b)+(z[32+2*i+1]+z[32+2*j])*y*y+(z[94+2*i+1]+z[94+2*j])*y
  a=als[i];u=ys[11+(i-1)%9];v=ys[11+i];w=ws[i];L=math.atan2(v*math.sin(a),u-v*math.cos(a));T=pi-a-L
  D+=rrr**2*u*v*math.sin(a)/2+(w-math.sin(w))/2+z[71]*w-z[i]*a-z[32+2*i]*u*u-z[32+2*i+1]*v*v-z[94+2*i]*u-z[94+2*i+1]*v+z[112+(i-1)%9]*L+z[112+i]*T+(z[112+(i-1)%9]+z[112+i])*w/2
 slack=pi-(A+B)@x0;expected=area+z[50:71]@slack+z[71]*(sum(ws)-2*pi)+z[112:]@cls
 err=float(abs(D-expected));assert err<1e-10;reports.append({'stem':stem,'scalar_identity_error':err,'area':area,'max_normalized_radius':float(max(ys)),'note':'375 candidate is OUTSIDE y<=1 domain; identity only, no bound calibration there'})
(P/'q0_closure_scalar_control.json').write_text(json.dumps(reports,indent=2));print(reports)
