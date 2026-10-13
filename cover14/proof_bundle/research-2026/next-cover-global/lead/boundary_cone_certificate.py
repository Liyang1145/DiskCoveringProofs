"""One saved-partition cone face support certificate; no new mesh search."""
from all_face_consistency_certificate import *
# Conservative exact upper bound on sqrt(1-U²), gives LOWER k and weaker valid cone cap.
s_upper=Q('0.943373658');assert s_upper*s_upper>=1-U*U
k_lower=U/s_upper

def cap_upper(box,boundary_positions):
 D=Q(1)
 for j in boundary_positions:
  vals=[]
  for t in box[j]:
   sn,cs=trig(PI*I(t));vals.append((cs+I(k_lower)*sn).lo)
  D=max(D,Q(min(vals),S))
 return 1/D

def cone_boxbound(box,p,opts,bb):
 old=boxbound(box,p,opts);X=cap_upper(box,bb)
 if X==1:return old
 val=I(0)
 for(lo,hi),pot in zip(box,p):
  aa=U*U*X;pf=float(pot);af=float(aa);opt=0 if pf>=af else(math.pi if pf<=-af else math.acos(pf/af));tf=max(float(lo)*math.pi,min(float(hi)*math.pi,opt));t=max(Q(0),min(Q('3.141592653589'),Q(format(tf,'.12f'))));sn,cs=sc(t);slope=I(aa)*cs-pot;vv=[PI*I(lo)*slope,PI*I(hi)*slope];val+=I(aa)*(sn-I(t)*cs)+I(max(v.lo for v in vv),max(v.hi for v in vv),True)
 return I(min(old.lo,val.lo),min(old.hi,val.hi),True)

if __name__=='__main__':
 start=time.time();allrows=json.loads((P/'all-face-consistency-catalogue.json').read_text())['runs'];rec=next(x for x in allrows if x['row']['family']=='10/4'and x['row']['index']==547);row=rec['row'];faces=json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][547]['faces'];ee=[[tuple(sorted(e))for e in combinations(f,2)]for f in faces];edges=sorted(set(e for es in ee for e in es));boundary={e for e in edges if sum(e in es for es in ee)==1};t=list(map(Q,row['rational_angles']));y=list(map(Q,row['rational_potentials']));nu=Q(row['rational_nu']);lam=Q(row['rational_lambda']);w=list(map(Q,row['rational_face_weights']));pp=[list(map(Q,rr))for rr in row['rational_face_potentials']];base=verify(10,[],t,y,nu,lam)
 for u,v in edges:
  inc=[(f,ee[f].index((u,v)))for f in range(len(faces))if (u,v)in ee[f]];c=1-sum(w[f]for f,j in inc);assert c>=0;pot=y[u]+y[v]-sum(pp[f][j]for f,j in inc);a=U*U*c;pf=float(pot);af=float(a);opt=0 if pf>=af else(math.pi if pf<=-af else math.acos(pf/af));x=max(Q(0),min(Q('3.141592653589'),Q(format(opt,'.12f'))));sn,cs=sc(x);slope=I(a)*cs-pot;base+=I(a)*(sn-I(x)*cs)+PI*I(max(0,slope.lo),max(0,slope.hi),True)
 parts={x['face']:x for x in rec['certificate']['parts']};oldtotal=base;newtotal=base;improved=[]
 for f in range(len(faces)):
  if w[f]==0:
   term=PI*sum(max(Q(0),-v)for v in pp[f]);oldtotal+=term;newtotal+=term;continue
  p=[v/w[f]for v in pp[f]];opts=[0 if float(v)>=float(U*U)else(math.pi if float(v)<=-float(U*U)else math.acos(float(v/(U*U))))for v in p];bb=[j for j,e in enumerate(ee[f])if e in boundary];ob=[];nb=[]
  for leaf in parts[f]['leaves']:
   box=[tuple(map(Q,seg))for seg in leaf];o=boxbound(box,p,opts);n=cone_boxbound(box,p,opts,bb);ob.append(o.hi);nb.append(n.hi)
  oldtotal+=I(max(ob),max(ob),True)*w[f];newtotal+=I(max(nb),max(nb),True)*w[f];improved.append({'face':f,'old_support':max(ob)/S,'cone_support':max(nb)/S,'boundary_positions':bb})
 out={'status':'excluded_pending_independent_replay'if newtotal.hi<0 else'inconclusive','family':'10/4','index':547,'upper_exact':str(Q(newtotal.hi,S)),'upper_display':newtotal.hi/S,'old_upper_display':oldtotal.hi/S,'s_upper':str(s_upper),'face_comparisons':improved,'seconds':time.time()-start};(P/'boundary-cone-certificate.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k!='face_comparisons'},flush=True)
