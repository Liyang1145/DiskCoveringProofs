"""Fresh convex fixed-anchor support proposals; floats never prove exclusion."""
from pathlib import Path
from fractions import Fraction as Q
import json,sys,math,os
import numpy as np
from scipy.optimize import minimize,Bounds,LinearConstraint

HERE=Path(__file__).resolve().parent
domains=json.loads((HERE/'DOMAIN-RECONSTRUCTION.json').read_text())
model=json.loads((HERE/'RECOVERED-PHYSICAL-GRAPH.json').read_text())
leaves=domains['pending_closed_leaf_boxes']
leaf_index=int(sys.argv[1]) if len(sys.argv)>1 else min(leaves,key=lambda row:sum(float(Q(b)-Q(a)) for a,b in zip(row['lower'],row['upper'])))['index']
leaf=next(row for row in leaves if row['index']==leaf_index)
stage=os.environ.get('N26_STAGE','');stem='leaf-'+str(leaf_index)+('-'+stage if stage else '')
lo=np.array([float(Q(x)) for x in leaf['lower']]);hi=np.array([float(Q(x)) for x in leaf['upper']])
mid=(lo+hi)/2
scale=int(domains['scale']);matrix=np.array([[float(Q(int(x),scale)) for x in row] for row in domains['matrix']])
A=[];b=[]
for i in range(16):
    for j in range(16):
        if i==j:continue
        row=np.zeros(15)
        if j:row[j-1]+=1
        if i:row[i-1]-=1
        A.append(row);b.append(matrix[i,j])
A=np.array(A);b=np.array(b)
reference=minimize(lambda x:sum((x-mid)**2),mid,jac=lambda x:2*(x-mid),
    bounds=Bounds(lo,hi),constraints=LinearConstraint(A,-np.inf,b),method='SLSQP',
    options={'ftol':1e-14,'maxiter':300})
angles=np.r_[0,reference.x];anchors=np.column_stack([np.cos(2*np.pi*angles),np.sin(2*np.pi*angles)])
edges=np.array(model['edges'],dtype=int)
weights=np.array([float(x) for x in json.loads((HERE/'supports/support-00.json').read_text())['kernel_certificate']['weight_numerators']]);weights/=sum(weights)
lap=np.zeros((76,76))
for (u,v),w in zip(edges,weights):lap[u,u]+=w;lap[v,v]+=w;lap[u,v]-=w;lap[v,u]-=w
positions=np.linalg.solve(lap[16:,16:],-lap[16:,:16]@anchors)

def points(x):return np.vstack([anchors,x[:120].reshape(60,2)])

proposals=[]
for owner in [16,25]:
    previous=os.environ.get('N26_REFERENCE_STAGE')
    if previous is not None:
        priorstem='leaf-'+str(leaf_index)+('' if previous=='base' else '-'+previous)
        prior=json.loads((HERE/'fresh-exclusions'/(priorstem+'-proposal.json')).read_text())
        prior=next(row for row in prior if row['origin_owner']==owner)
        prior_kernel=json.loads((HERE/'fresh-kernels'/(priorstem+'-VERIFIED.json')).read_text())
        prior_kernel=next(row for row in prior_kernel['kernels'] if row['origin_owner']==owner)
        reference.x=np.array([float(Q(a)+Q(b)) for a,b in zip(prior_kernel['reference_turns'],prior['quadratic_tangent'])])
        angles=np.r_[0,reference.x];anchors=np.column_stack([np.cos(2*np.pi*angles),np.sin(2*np.pi*angles)])
        positions=np.linalg.solve(lap[16:,16:],-lap[16:,:16]@anchors)
    def inequality(x):
        P=points(x);differences=P[edges[:,0]]-P[edges[:,1]]
        return np.r_[x[-1]-np.sum(differences*differences,axis=1),x[-1]-sum(P[16+owner]**2)]
    def jacobian(x):
        P=points(x);differences=P[edges[:,0]]-P[edges[:,1]]
        out=np.zeros((135,121));out[:,-1]=1
        for i,(u,v) in enumerate(edges):
            if u>=16:out[i,2*(u-16):2*(u-16)+2]-=2*differences[i]
            if v>=16:out[i,2*(v-16):2*(v-16)+2]+=2*differences[i]
        out[-1,2*owner:2*owner+2]=-2*P[16+owner]
        return out
    x0=np.r_[positions.ravel(),.06];x0[-1]-=min(0,min(inequality(x0)))
    objective=lambda x:x[-1]
    gradient=np.r_[np.zeros(120),1]
    answer=minimize(objective,x0,jac=lambda x:gradient,method='SLSQP',
        bounds=[(None,None)]*120+[(0,None)],constraints={'type':'ineq','fun':inequality,'jac':jacobian},
        options={'ftol':2e-13,'maxiter':500})
    multipliers=getattr(answer,'multipliers',None)
    if multipliers is None:raise RuntimeError('Installed SLSQP did not expose proposal multipliers')
    scale=10**12;integer_weights=[max(1,round(float(v)*scale)) for v in multipliers]
    row={'leaf_index':leaf_index,'stage':stage,'origin_owner':owner,'reference_turns':[format(x,'.17g') for x in reference.x],
        'source_lower':leaf['lower'],'source_upper':leaf['upper'],
        'weight_scale':scale,'weight_numerators':integer_weights,
        'success':bool(answer.success),'message':answer.message,'iterations':answer.nit,
        'point_radius_proposal':math.sqrt(max(0,answer.fun)),'minimum_constraint_proposal':float(min(inequality(answer.x))),
        'root_radius_comparison_proposal':math.sqrt(max(0,answer.fun))-.23470009040044824,
        'note':'Fixed-anchor convex numerical proposal only; exact whole-box proof required.'}
    proposals.append(row);print(json.dumps({k:v for k,v in row.items() if k not in ['weight_numerators','reference_turns','source_lower','source_upper']},indent=2),flush=True)
dest=HERE/'fresh-support-proposals';dest.mkdir(exist_ok=True)
(dest/(stem+'.json')).write_text(json.dumps(proposals,indent=2)+'\n')
