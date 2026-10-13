"""Numeric mechanism test only: root adversarial lambda and angular concavity Jensen loss."""
from multifield_simplex_pilot import *
D0=json.loads((P/'multifield_simplex_pilot.json').read_text())
fields=[field([[F(x) for x in q] for q in f['forces']],f['name']) for f in D0['fields']]
v=[[F(i==j) for i in range(9)] for j in range(9)]
A=table(v,fields);arr=np.array([[float(lo(x)) for x in row] for row in A]);m=len(fields)
res=linprog(np.r_[np.zeros(9),1.0],A_ub=np.c_[arr,-np.ones(m)],b_ub=np.zeros(m),A_eq=[np.r_[np.ones(9),0]],b_eq=[1],bounds=[(0,None)]*9+[(None,None)],method='highs')
assert res.success
y=[F(max(0,round(x*10**12)),10**12) for x in res.x[:9]];s=sum(y);y=[x/s for x in y]
th=angles(y)
works=[sum(I(f['loads'][i][0])*iv.cos(th[i])+I(f['loads'][i][1])*iv.sin(th[i]) for i in range(9)) for f in fields]
report={'label':'numeric mechanism diagnostic only, no domain exclusion','adversarial_y':[str(x) for x in y],'game_value':float(res.fun),'true_support_max_lower':str(max(lo(w) for w in works)),'works':[(f['name'],str(lo(w))) for f,w in zip(fields,works)],'widths':[float(lo(L-D*I(x))) for x in y]}
(P/'root_game_diagnostic.json').write_text(json.dumps(report,indent=2));print(report)
