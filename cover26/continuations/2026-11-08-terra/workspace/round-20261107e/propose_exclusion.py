"""Numerical choices for a fully exact closed-box energy certificate."""
from pathlib import Path
from fractions import Fraction as Q
import json,sys,math,os
import numpy as np
from scipy.optimize import minimize,Bounds,LinearConstraint,linprog
import exact_energy as exact

HERE=Path(__file__).resolve().parent
leaf_index=int(sys.argv[1]) if len(sys.argv)>1 else 2136
parts=int(sys.argv[2]) if len(sys.argv)>2 else 8
stage=os.environ.get('N26_STAGE','');stem='leaf-'+str(leaf_index)+('-'+stage if stage else '')
domains=json.loads((HERE/'DOMAIN-RECONSTRUCTION.json').read_text())
leaf=next(r for r in domains['pending_closed_leaf_boxes'] if r['index']==leaf_index)
kernels=json.loads((HERE/'fresh-kernels'/(stem+'-VERIFIED.json')).read_text())['kernels']
out=[]
for kernel in kernels:
    info=exact.data(kernel,leaf,parts)
    H=np.array([[float(x) for x in row] for row in info['hessian']])
    eig=np.linalg.eigvalsh(H[6:,6:])[0]
    rest=Q(max(0,math.ceil((-eig+1e-5)*10**8)),10**8)
    correction=[Q(10**8)]*6+[rest]*9
    matrix,linear,constant,pivots=exact.quadratic(info,correction)
    QQ=np.array([[float(x) for x in row] for row in matrix]);ll=np.array(list(map(float,linear)))
    low=np.array(list(map(float,info['lower_delta'])));high=np.array(list(map(float,info['upper_delta'])))
    middle=(low+high)/2;width=(high-low)/2
    reference=np.array(list(map(float,info['reference'])))
    scale=int(domains['scale']);A=[];rhs=[];labels=[]
    for i in range(16):
        for j in range(16):
            if i==j:continue
            row=np.zeros(15)
            if j:row[j-1]+=1
            if i:row[i-1]-=1
            A.append(row);labels.append((i,j))
            rhs.append(float(Q(int(domains['matrix'][i][j]),scale))-(reference[j]-reference[i]))
    A=np.array(A);rhs=np.array(rhs)
    function=lambda z:.5*(middle+width*z)@QQ@(middle+width*z)+ll@(middle+width*z)
    derivative=lambda z:width*(QQ@(middle+width*z)+ll)
    ans=minimize(function,np.zeros(15),jac=derivative,bounds=Bounds(-np.ones(15),np.ones(15)),
        constraints=LinearConstraint(A*width,-np.inf,rhs-A@middle),method='SLSQP',
        options={'ftol':1e-14,'maxiter':300})
    point=[Q(format(x,'.17g')) for x in middle+width*ans.x]
    Qp=[sum(a*b for a,b in zip(row,point)) for row in matrix]
    tangent=np.array([float(a+b) for a,b in zip(Qp,linear)])
    lp=linprog(tangent,A_ub=A,b_ub=rhs,bounds=list(zip(low,high)),method='highs')
    if not lp.success:raise ValueError('difference dual proposal failed: '+lp.message)
    denominator=10**18;terms=[]
    for (i,j),value in zip(labels,lp.ineqlin.marginals):
        n=max(0,round(-float(value)*denominator))
        if n:terms.append([i,j,str(n)])
    dual={'denominator':str(denominator),'terms':terms}
    lower,pivots=exact.evaluate(info,list(map(str,correction)),list(map(str,point)),dual,domains['matrix'],scale)
    radius=Q(domains['radius_upper']);gap=lower-radius*radius
    row={'leaf_index':leaf_index,'origin_owner':kernel['origin_owner'],'parts':parts,
         'curvature_correction':list(map(str,correction)),'quadratic_tangent':list(map(str,point)),
         'difference_dual':dual,'exact_energy_lower':str(lower),'exact_strict_gap':str(gap),
         'kernel_source_sha256':kernel['source_kernel_sha256'],'passed_exact_margin_proposal':gap>0,
         'note':'Choices only; fresh verification must reconstruct every premise.'}
    out.append(row)
    print('leaf',leaf_index,'owner',kernel['origin_owner'],'sub-Hessian eigen proposal',eig,
          'exact gap',float(gap),'QP',ans.success,'LP terms',len(terms),flush=True)
dest=HERE/'fresh-exclusions';dest.mkdir(exist_ok=True)
(dest/(stem+'-proposal.json')).write_text(json.dumps(out,indent=2)+'\n')
