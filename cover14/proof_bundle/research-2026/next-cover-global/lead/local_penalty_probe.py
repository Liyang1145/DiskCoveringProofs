"""Choose penalty for explicit neighborhood, numerical proposal only."""
import local_sosc_certificate as b
import numpy as np,json
H=np.array([[b.mid(x)for x in row]for row in b.HL]);G=np.array([[b.mid(x)for x in b.grads[k]]for k in b.positive]);gauge=np.zeros((28,28));gauge[19,19]=1
out=[]
for K in[1,3,10,30,100,300,1000]:
 A=H+K*(G.T@G+gauge);ev=np.linalg.eigvalsh(A);out.append({'K':K,'min_eigenvalue':float(ev[0]),'max_eigenvalue':float(ev[-1]),'min_lambda':min(b.mid(b.lam[k])for k in b.positive)})
(b.P/'local-penalty-probe.json').write_text(json.dumps({'status':'numeric_proposals_only','runs':out},indent=2));print(out)
