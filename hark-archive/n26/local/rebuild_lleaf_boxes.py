"""Rebuild boxes of ALL LOCAL-SLAB leaves by replaying SPLIT+tighten from root (as v3replay/replay.py); compare with disk leaf files.
Writes local/lleaf_boxes.json atomically. Float-free (Fractions)."""
import sys,json,os,time,glob
from fractions import Fraction as F
SRC='/workspace/work/dcp-n26/repo/cover26/proof_bundle/outputs/n26-sharp-candidate-angles-published-replay-v1'
sys.path.insert(0,SRC)
from n26_force import angular_domain, rootbox, tighten
P=json.load(open('/workspace/work/dcp-n26/repo/cover26/proof_bundle/work/n26-sharp-candidate-angles-proposal-v3.json'))
T=json.load(open('/workspace/work/dcp-n26/v3replay/V3-REPLAY-TREE.json'))['nodes']
mat=angular_domain(P['spec']);lo,hi=rootbox(mat)
import pickle
CK='/workspace/work/dcp-n26/local/lleaf_ck.pkl'
if os.path.exists(CK):st,out=pickle.load(open(CK,'rb'))
else:st=[(0,lo,hi,0)];out={}
t0=time.time();BUD=float(sys.argv[1]) if len(sys.argv)>1 else 95
while st:
    if time.time()-t0>BUD:
        pickle.dump((st,out),open(CK+'.tmp','wb'));os.replace(CK+'.tmp',CK)
        print('PAUSED stack',len(st),'leaves so far',len(out));sys.exit(0)
    i,lo,hi,top=st.pop();n=T[i]
    if n['kind']=='EMPTY':continue
    b=tighten(mat,lo,hi)
    if b is None:continue
    lo,hi=b
    if n['kind']=='SPLIT':
        a=n['axis'];m=F(n['mid']);assert lo[a]<m<hi[a]
        lu=list(hi);lu[a]=m;rl=list(lo);rl[a]=m
        c=n['children'];t=top
        if i==0:pass
        st.append((c[1],rl,list(hi),c[1] if i==0 else top));st.append((c[0],list(lo),lu,c[0] if i==0 else top));continue
    if n['kind']=='LOCAL-SLAB':out[i]={'top':top,'lo':[str(x) for x in lo],'hi':[str(x) for x in hi]}
print('LS leaves',len(out),time.time()-t0)
# compare with disk
bad=0;chk=0;miss=[]
disk={}
for f in glob.glob('/workspace/work/dcp-n26/v3replay/lleaves/*/s*.json'):
    disk[int(os.path.basename(f)[1:-5])]=f
for i,v in out.items():
    if i in disk:
        d=json.load(open(disk[i]));chk+=1
        if [F(x) for x in d['lower']]!=[F(x) for x in v['lo']] or [F(x) for x in d['upper']]!=[F(x) for x in v['hi']]:bad+=1
    else:miss.append(i)
print('disk compared',chk,'mismatch',bad,'missing',len(miss),'disk-not-in-tree',len(set(disk)-set(out)))
json.dump({'leaves':out,'compared':chk,'mismatch':bad,'missing':miss},open('local/lleaf_boxes.json.tmp','w'))
os.replace('local/lleaf_boxes.json.tmp','local/lleaf_boxes.json')
