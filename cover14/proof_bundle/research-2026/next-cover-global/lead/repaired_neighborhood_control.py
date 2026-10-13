"""Check whether repaired numeric points enter certified local box after gauge. Not exact covers."""
from coupled_primal_probe import *
if __name__=='__main__':
 data=json.loads((P/'cyclicity-repair-control.json').read_text())['runs'];out=[]
 for row in data:
  V=np.array(row['geometry']['centers']);p=V[9];ang=-math.atan2(p[1],p[0]);rot=np.array([[math.cos(ang),-math.sin(ang)],[math.sin(ang),math.cos(ang)]]);V=V@rot.T
  # The triangle reconstruction may differ by a rotation pi; preserve exact labels.
  if np.max(abs(V-C))>np.max(abs(-V-C)):V=-V
  out.append({'start':row['start'],'max_aligned_coordinate_error':float(np.max(abs(V-C))),'inside_certified_box_numerically':bool(np.max(abs(V-C))<=2e-5),'max_equation_residual':row['max_residual'],'anchor_error':row['geometry']['max_unit_anchor_error']})
 (P/'repaired-neighborhood-control.json').write_text(json.dumps({'status':'numeric_membership_test_not_covercertificate','runs':out},indent=2));print(out)
