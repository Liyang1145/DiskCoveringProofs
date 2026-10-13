"""Continuum support for fixed rational all-face factor-dual parameters."""
from lower_branch_box_kernel import *
from joint_innernorm_probe import fn,fval,lines,verts,brentq

def prepare(q,edges,faces,proposal):
 y=[Q(format(v,'.12f'))for v in proposal['potentials']];nu=max(Q(0),Q(format(proposal['nu'],'.12f')));lam=max(Q(0),Q(format(proposal['lambda'],'.12f')))
 w=[Q(math.floor(max(0,v)*(1-1e-10)*10**12),10**12)for v in proposal['weights']];pp=[[Q(format(v,'.12f'))for v in rr]for rr in proposal['face_potentials']];ts=[]
 for j in range(q):
  pts=[0,float((verts[1][0].lo+verts[1][0].hi)/(2*S)),float((verts[2][0].lo+verts[2][0].hi)/(2*S)),math.pi];cand=list(pts)
  for seg in range(3):
   slope=float(lines[seg][1]);g=lambda t:fn(t,float(nu))+float(lam)*slope-float(y[j]);lo,hi=pts[seg],pts[seg+1]
   if g(lo)>0 and g(hi)<0:cand.append(brentq(g,lo,hi))
  t=max(cand,key=lambda t:fval(t,float(nu))+float(lam)*min(float(a)+float(k)*t for a,k in lines)-float(y[j])*t);ts.append(max(Q(0),min(Q('3.141592653589'),Q(format(t,'.12f')))))
 return {'family':proposal['family'],'index':proposal['index'],'rational_angles':list(map(str,ts)),'rational_potentials':list(map(str,y)),'rational_nu':str(nu),'rational_lambda':str(lam),'rational_face_weights':list(map(str,w)),'rational_face_potentials':[[str(v)for v in rr]for rr in pp]}

def certify(q,edges,faces,row,budget=24000):
 t=list(map(Q,row['rational_angles']));y=list(map(Q,row['rational_potentials']));nu=Q(row['rational_nu']);lam=Q(row['rational_lambda']);w=list(map(Q,row['rational_face_weights']));pp=[list(map(Q,rr))for rr in row['rational_face_potentials']];ee=[[tuple(sorted(e))for e in combinations(f,2)]for f in faces];base=verify(q,[],t,y,nu,lam)
 for u,v in edges:
  inc=[(f,ee[f].index((u,v)))for f in range(len(faces))if (u,v)in ee[f]];c=1-sum(w[f]for f,j in inc);assert c>=0;pot=y[u]+y[v]-sum(pp[f][j]for f,j in inc);a=U*U*c;pf=float(pot);af=float(a);opt=0 if pf>=af else(math.pi if pf<=-af else math.acos(pf/af));x=max(Q(0),min(Q('3.141592653589'),Q(format(opt,'.12f'))));sn,cs=sc(x);slope=I(a)*cs-pot;base+=I(a)*(sn-I(x)*cs)+PI*I(max(0,slope.lo),max(0,slope.hi),True)
 data=[];uid=0
 for f in range(len(faces)):
  if w[f]==0:
   base+=PI*sum(max(Q(0),-v)for v in pp[f]);continue
  p=[v/w[f]for v in pp[f]];opts=[0 if float(v)>=float(U*U)else(math.pi if float(v)<=-float(U*U)else math.acos(float(v/(U*U))))for v in p];box=[(Q(0),Q(1))]*3;b=boxbound(box,p,opts)*w[f];data.append((f,p,opts,[(-b.hi,0,box)]))
 for k in range(budget):
  upper=base.hi-sum(d[3][0][0]for d in data)
  if upper<0:break
  f,p,opts,heap=data[k%len(data)];neg,_,box=heapq.heappop(heap);j=max(range(3),key=lambda j:box[j][1]-box[j][0]);lo,hi=box[j];mid=(lo+hi)/2
  for seg in[(lo,mid),(mid,hi)]:
   b=box.copy();b[j]=seg;uid+=1;v=boxbound(b,p,opts)*w[f];heapq.heappush(heap,(-v.hi,uid,b))
 upper=base.hi-sum(d[3][0][0]for d in data)
 return {'status':'excluded'if upper<0 else'inconclusive','upper_display':upper/S,'upper_exact':str(Q(upper,S)),'parts':[{'face':f,'leaves':[[[str(a),str(b)]for a,b in box]for neg,uid,box in heap]}for f,p,o,heap in data]}
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());proposals=json.loads((P/'all-face-consistency-probe.json').read_text())['runs'];G=json.loads((P/'stress-barycentric-result.json').read_text());out=[];start=time.time()
 for proposal in proposals:
  fam=proposal['family'];idx=proposal['index'];q=10 if fam=='candidate'else int(fam.split('/')[0]);faces=([x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]])if fam=='candidate'else(D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces']);edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});row=prepare(q,edges,faces,proposal);cert=certify(q,edges,faces,row,24000);assert fam!='candidate'or cert['status']!='excluded';out.append({'row':row,'certificate':cert});print(fam,idx,cert['status'],cert['upper_display'],'seconds',time.time()-start,flush=True);sc.cache_clear();costerm.cache_clear()
 (P/'all-face-consistency-certificate.json').write_text(json.dumps({'status':'interval_factor_dual_pending_replay','runs':out},indent=2))
