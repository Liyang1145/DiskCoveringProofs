import json,os,subprocess,shutil,time,urllib.request,concurrent.futures as cf
DEST='/workspace/work/dcp-n11-lean/wip-build/mlib'
LT='/var/tmp/lean/lean-4.33.1-linux_aarch64/bin/leantar'
LOG='/workspace/work/dcp-n11-lean/wip-build/logs/fetch.log'
DONE='/var/tmp/wb/fetch_done.txt'
res=json.load(open('/var/tmp/wb/sizes.json'))
done=set(open(DONE).read().split()) if os.path.exists(DONE) else set()
todo=[r for r in res if r[0] not in done]
def log(s):
    open(LOG,'a').write(time.strftime('%H:%M:%S ')+s+'\n')
def avail():
    st=os.statvfs('/'); return st.f_bavail*st.f_frsize
def memavail():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable'): return int(l.split()[1])*1024
def dl(r):
    m,f,c,n=r; p='/var/tmp/stage/'+f
    for k in range(4):
        try: urllib.request.urlretrieve(f'https://lakecache.blob.core.windows.net/{c}/f/{f}',p); return p
        except Exception as e: time.sleep(2)
    raise RuntimeError(m)
B=150
log(f'start todo={len(todo)}')
for i in range(0,len(todo),B):
    while avail()<2.3e9 or memavail()<1.5e9:
        log(f'wait disk={avail()/1e9:.2f} mem={memavail()/1e9:.2f}'); time.sleep(20)
    batch=todo[i:i+B]
    shutil.rmtree('/var/tmp/stage',ignore_errors=True); os.makedirs('/var/tmp/stage')
    with cf.ThreadPoolExecutor(16) as ex: files=list(ex.map(dl,batch))
    subprocess.run([LT,'-C','/var/tmp/stage/x','-x']+files,check=True)
    for f in files: os.remove(f)
    n=0
    for dp,dn,fn in os.walk('/var/tmp/stage/x'):
        if '/.lake/build/lib/lean' not in dp+'/': continue
        rel=dp.split('/.lake/build/lib/lean',1)[1].lstrip('/')
        for x in fn:
            if x.endswith(('.olean','.olean.private','.olean.server','.ir')):
                d=os.path.join(DEST,rel); os.makedirs(d,exist_ok=True)
                shutil.copyfile(os.path.join(dp,x),os.path.join(d,x)); n+=1
    open(DONE,'a').write(''.join(r[0]+'\n' for r in batch))
    log(f'batch {i//B} done files={n} total_done={i+len(batch)} disk={avail()/1e9:.2f} mem={memavail()/1e9:.2f}')
shutil.rmtree('/var/tmp/stage',ignore_errors=True)
log('ALL DONE')
