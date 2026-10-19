import subprocess,sys,json,time
T0=time.time(); BUD=float(sys.argv[1])
for sh in (0,1):
    left=BUD-(time.time()-T0)
    if left<20: break
    o=subprocess.run(['python3','certB_v3.py',str(left),str(sh),'2'],capture_output=True,text=True)
    if o.returncode: print(o.stderr[-2000:]); sys.exit(1)
    r=json.loads(o.stdout.strip().splitlines()[-1]); print(sh,r['done'],'/',r['leaves_in_shard'],r['complete'])
    if not r['complete']: break
