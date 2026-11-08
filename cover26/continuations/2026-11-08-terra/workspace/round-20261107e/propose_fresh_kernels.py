"""Create exact inverse proposals for fresh positive origin-conditional kernels."""
from pathlib import Path
from fractions import Fraction as Q
import json,sys,os
import sympy as sp
from sympy.polys.matrices import DomainMatrix
from sympy.polys.domains import ZZ

HERE=Path(__file__).resolve().parent
leaf=int(sys.argv[1]) if len(sys.argv)>1 else 2136
stage=os.environ.get('N26_STAGE','');stem='leaf-'+str(leaf)+('-'+stage if stage else '')
proposals=json.loads((HERE/'fresh-support-proposals'/(stem+'.json')).read_text())
edges=json.loads((HERE/'RECOVERED-PHYSICAL-GRAPH.json').read_text())['edges']
dest=HERE/'fresh-kernels';dest.mkdir(exist_ok=True)
for row in proposals:
    owner=row['origin_owner'];weights=row['weight_numerators']
    B=[[0]*60 for _ in range(60)]
    for (u,v),w in zip(edges,weights):
        if u>=16:B[u-16][u-16]+=w
        if v>=16:B[v-16][v-16]+=w
        if u>=16 and v>=16:B[u-16][v-16]-=w;B[v-16][u-16]-=w
    B[owner][owner]+=weights[-1]
    dm=DomainMatrix.from_Matrix(sp.Matrix(B)).convert_to(ZZ)
    numerator,denominator=dm.inv_den(method='rref')
    matrix=numerator.to_Matrix();denominator=int(denominator)
    values=[[int(matrix[i,j]) for j in range(60)] for i in range(60)]
    if denominator<0:denominator=-denominator;values=[[-x for x in r] for r in values]
    out={**row,'inverse_denominator':str(denominator),'inverse_numerators':[[str(x) for x in r] for r in values],
         'note':'Exact inverse proposal; verify_fresh_kernels.py must validate it independently.'}
    path=dest/(stem+'-owner-'+str(owner)+'.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print('proposed exact inverse',leaf,owner,'denominator digits',len(str(denominator)),flush=True)
