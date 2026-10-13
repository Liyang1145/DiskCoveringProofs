"""Bounded numeric stress calibration for observed triangle-fan candidate.
Purpose: whether fixed-anchor network admits positive optimal stress and angular
Hessian has local positive curvature. No global or interval conclusion."""
from pathlib import Path
import json, numpy as np
from scipy.linalg import null_space
P=Path(__file__).resolve().parents[1]
j=json.loads((P/'evidence/d3-chart-calibration.json').read_text())
a,t,r,w=map(float,j['root']); b=(1+a+r)/2;v=w/np.sqrt(3)
beta=np.arctan2(v,b);rot=lambda ang:np.array([[np.cos(ang),-np.sin(ang)],[np.sin(ang),np.cos(ang)]])
sites=[]
for k in range(3):
    R=rot(2*np.pi*k/3)
    sites.extend([R@np.array([b,v]),rot(2*np.pi*k/3+np.pi/3)@np.array([t,0]),rot(2*np.pi*(k+1)/3)@np.array([b,-v])])
for k in range(3):sites.append(rot(2*np.pi*k/3)@np.array([a,0]))
angles=np.array([2*beta,2*np.pi/3-2*beta,2*np.pi/3,2*np.pi/3+2*beta,4*np.pi/3-2*beta,4*np.pi/3,4*np.pi/3+2*beta,2*np.pi-2*beta,2*np.pi])
anchors=np.array([[np.cos(x),np.sin(x)] for x in angles])
faces=[(8,0,9),(2,3,10),(5,6,11),(9,10,1),(10,11,4),(11,9,7)]
wits=[rot(2*np.pi*k/3)@np.array([a+r,0]) for k in range(3)]+[rot(2*np.pi*k/3+np.pi/3)@np.array([t-r,0]) for k in range(3)]
Z=np.array(sites+wits+list(anchors)); edges=[]
for i in range(9):edges.extend([(18+i,i),(18+i,(i+1)%9)])
for i,f in enumerate(faces):edges.extend([(12+i,k) for k in f])
A=np.zeros((36,len(edges)))
for e,(i,k) in enumerate(edges):
    d=Z[i]-Z[k]
    if i<18:A[2*i:2*i+2,e]+=d
    if k<18:A[2*k:2*k+2,e]-=d
N=null_space(A,rcond=1e-10)
alpha=N[:,0]/N[:,0].sum()
L=np.zeros((27,27))
for weight,(i,k) in zip(alpha,edges):
    L[i,i]+=weight;L[k,k]+=weight;L[i,k]-=weight;L[k,i]-=weight
Q=L[18:,18:]-L[18:,:18]@np.linalg.solve(L[:18,:18],L[:18,18:])
H=np.zeros((9,9));grad=np.zeros(9)
for i in range(9):
 for k in range(i+1,9):
    q=-Q[i,k]; theta=angles[i]-angles[k]
    grad[i]+=2*q*np.sin(theta);grad[k]-=2*q*np.sin(theta)
    z=2*q*np.cos(theta);H[i,i]+=z;H[k,k]+=z;H[i,k]-=z;H[k,i]-=z
out={'level':'numeric only fixed candidate stress calibration','nullity':int(N.shape[1]),'weights':alpha.tolist(),'min_weight':float(alpha.min()),'equilibrium_residual':float(np.max(np.abs(A@alpha))),'edge_length_residual':float(max(abs(np.linalg.norm(Z[i]-Z[k])-r) for i,k in edges)),'energy':float(np.trace(anchors.T@Q@anchors)),'r_squared':r*r,'angular_gradient':grad.tolist(),'angular_hessian_eigenvalues':np.linalg.eigvalsh(H).tolist(),'edges':edges,'faces':faces,'angles':angles.tolist(),'schur':Q.tolist()}
(P/'evidence/candidate-stress-probe.json').write_text(json.dumps(out,indent=2))
print(json.dumps({k:out[k] for k in ['nullity','min_weight','equilibrium_residual','edge_length_residual','energy','r_squared','angular_hessian_eigenvalues']}))
