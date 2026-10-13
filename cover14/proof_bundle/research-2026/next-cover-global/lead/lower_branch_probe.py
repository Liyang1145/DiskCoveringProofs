"""Bounded mechanism: candidate plus12 closest sharedradius survivors; lowerbranch loss."""
from lower_branch_reopt import *
from lower_branch_box_kernel import lower_loss
if __name__=='__main__':
 # Known exact pi/4 test: loss=3sqrt2/2-(sqrt2+1/2)=(sqrt2-1)/2.
 bx=[(Q(1,4),Q(1,4))]*3;L=lower_loss(bx);exact=(math.sqrt(2)-1)/2*float(U*U);assert 0<L.lo/S<=exact+1e-14
 G=json.loads((P/'stress-barycentric-result.json').read_text());faces=[x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});row=optimize(10,edges,faces,[14,15]);row.update(family='candidate',index=-1);cert=certify_pack(10,edges,faces,row,[14,15],6000);assert cert['status']!='excluded';out=[{'row':row,'certificate':cert}];print('candidate',row['sampled_lp_not_bound'],cert['upper_display'],flush=True)
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());data=json.loads((P/'shared-radius-catalogue.json').read_text())['runs'];old={(x['family'],x['index']):x for x in json.loads((P/'all-face-pack-catalogue.json').read_text())['runs']};selected=[]
 for fam in ['10/4','11/3']:selected+=sorted([x for x in data if x['row']['family']==fam and x['certificate']['status']!='excluded'],key=lambda x:x['row']['sampled_lp_not_bound'])[:6]
 for test in selected:
  fam=test['row']['family'];idx=test['row']['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});prior=old[fam,idx];pack=prior.get('faces')or[p['face']for p in prior.get('parts',[])];row=optimize(q,edges,faces,pack);row.update(family=fam,index=idx);cert=certify_pack(q,edges,faces,row,pack,6000);out.append({'row':row,'certificate':cert});print(fam,idx,row['sampled_lp_not_bound'],cert['status'],cert['upper_display'],flush=True);sc.cache_clear();costerm.cache_clear()
 (P/'lower-branch-probe.json').write_text(json.dumps({'status':'interval_lowerbranch_proposals_pending_replay','runs':out},indent=2))
