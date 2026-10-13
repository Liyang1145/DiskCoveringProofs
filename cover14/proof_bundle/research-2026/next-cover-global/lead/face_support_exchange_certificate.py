"""One bounded continuum certificate of repaired dual proposal, unchanged geometry/kernel."""
from all_face_consistency_certificate import *
if __name__=='__main__':
 start=time.time();proposal=json.loads((P/'face-support-exchange.json').read_text())['runs'][-1];faces=json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][547]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});row=prepare(10,edges,faces,proposal);cert=certify(10,edges,faces,row,24000);out={'status':'continuum_bound_pending_fraction_replay','row':row,'certificate':cert,'seconds':time.time()-start};(P/'face-support-exchange-certificate.json').write_text(json.dumps(out,indent=2));print(cert['status'],cert['upper_display'],'seconds',time.time()-start,flush=True)
