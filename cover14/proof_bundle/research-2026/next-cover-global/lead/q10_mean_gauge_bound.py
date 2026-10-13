"""Mean-prefix affine rotation proposal + exact Fraction bound, optional driver fallback."""
from q10_mean_gauge_control import *
from q10_polytope_partition_probe import L,S

def mean_bound(row,poly):
 TT=angles(poly);TT+=np.mean(np.arange(10)*float(L.lo/S)-TT,axis=1)[:,None]
 AA=np.c_[np.cos(TT.mean(axis=0)),np.sin(TT.mean(axis=0))];D=np.array(row['incidence_matrix']);nf=len(row['faces']);X=np.linalg.lstsq(D,np.vstack([np.zeros((3*nf,2)),np.repeat(AA,2,axis=0)]),rcond=None)[0]
 r=solve_case(row['case'],X[:14],AA,row['faces'],row['owners'],X[14:]);r.update(index=879,family='10/4');r=smooth(r,TT)
 c=dict(index=879,flow=certify(r,Q(0)),polytope={'vertices':poly.to_dict()['vertex_set']},gauge='mean_prefix')
 rr=gauge_replay(c);rr['lower_radius_exact']=rr['lower_exact'];rr['lower_radius_display']=rr['lower_display'];c.update(lower_radius_exact=rr['lower_exact'],lower_radius_display=rr['lower_display'],status='excluded_pending_fraction_replay'if rr['excluded']else'inconclusive')
 return r,c,rr
