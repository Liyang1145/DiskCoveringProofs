"""Numerical fixed-anchor optimal-stress tangent and critical-angle kernel. Not a certificate."""
import runpy,json
import numpy as np
from pathlib import Path
from scipy.linalg import null_space
P=Path(__file__).resolve().parent
d=runpy.run_path(str(P/'check_radial_network.py'))
A=d['A'];alpha=d['alpha'][d['active']];U=d['U'];X=d['X'];edges=d['edges'];active=d['active'];H=d['H'];Lam=d['Lam']
# Distance-force equilibrium, not the angular rows.
B=np.vstack([A[:44],A[-1:]])
N=null_space(B,rcond=1e-7)
# Squared-energy alpha: anchor angular derivatives = 2r * force tangential loads at harmonic candidate.
G=2*d['r']*A[44:53]@N
K=null_space(np.vstack([G.T,np.ones((1,9))]),rcond=1e-7)
Hcrit=K.T@H@K
report={'scope':'numeric at rounded solution; no exact-rank conclusion','B_singularvalues':np.linalg.svd(B,compute_uv=False).tolist(),'stress_tangent_dim':N.shape[1],'G_singularvalues':np.linalg.svd(G,compute_uv=False).tolist(),'angle_critical_dim_without_rotation':K.shape[1],'Hcrit_eigenvalues':np.linalg.eigvalsh(Hcrit).tolist(),'critical_basis':K.tolist(),'stress_tangent_basis':N.tolist(),'gradient_span':G.tolist()}
(P/'dual_envelope_check.json').write_text(json.dumps(report,indent=2))
print({k:v for k,v in report.items() if k not in ['B_singularvalues','critical_basis','stress_tangent_basis','gradient_span']})
