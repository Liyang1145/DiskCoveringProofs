import sys,os,json,time,glob
os.environ['VC_BUDGET']=sys.argv[1]
T0=time.time(); B=float(sys.argv[1])
sys.path.insert(0,'/workspace/work/dcp-n26')
import verify_certs as V
R='/workspace/work/dcp-n26/regress_v3.json'
st=json.load(open(R)) if os.path.exists(R) else {}
files=sorted(f for f in glob.glob('/workspace/work/dcp-n26/certs/*.json') if not f.endswith('.ckpt.json'))
for f in files:
    k=os.path.basename(f)
    if st.get(k,{}).get('final'): continue
    rem=B-(time.time()-T0)
    if rem<5: break
    os.environ['VC_BUDGET']=str(rem)
    V._BUD=rem
    s=V.check_file(f)
    s['final']=bool(s.get('CLOSED') or s.get('CLOSED_WITH_LOCAL_SLAB_FOREST') or s.get('fail') or s.get('open'))
    st[k]=s
    json.dump(st,open(R+'.tmp','w'),default=str); os.replace(R+'.tmp',R)
    open('/workspace/work/dcp-n26/ledger.jsonl','a').write(json.dumps({'t':time.strftime('%F %T'),'item':'regress343','file':k,'closed':s.get('CLOSED'),'deferred':s.get('deferred'),'pass':s.get('pass'),'fail':s.get('fail')})+'\n')
fin=sum(1 for v in st.values() if v.get('final'))
print('final',fin,'of',len(files),'elapsed',round(time.time()-T0))
