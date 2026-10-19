import sys,os,json,time
import bnb, lgeom
os.makedirs('fleaves',exist_ok=True)
T0=time.time(); BUD=float(sys.argv[1])
for t in sys.argv[2:]:
    tr,sl=lgeom.tree(t)
    for n,(m,lo,hi) in enumerate(sl):
        if m>=0: continue
        p=f'fleaves/{t}_s{n}.json'
        if os.path.exists(p) and json.load(open(p))['done']: continue
        left=BUD-(time.time()-T0)
        if left<5: print('budget stop'); sys.exit(0)
        r=bnb.run(t,left,path=p,box=(lo,hi)); r['slab']=n
        print(json.dumps(r),flush=True)
        with open('/workspace/work/dcp-n26/ledger.jsonl','a') as f: f.write(json.dumps({'event':'v3-outer-force',**r,'t':time.time()})+'\n')
print('ALL DONE')
