import subprocess,time,os,sys
order=[int(x) for x in sys.argv[1:]] or list(range(23,37))+list(range(12,23))+[11]
mods=[]
for k in order:
    mods+= [f"DCPN11Core/C450Replay/Seg{k}/Cells{j}" for j in range(1,5)]+[f"DCPN11Core/C450Replay/Seg{k}/All"]
todo=[m for m in mods if not os.path.exists(f"/tmp/lc/{m}.olean")]
t0=time.time(); run=[]; done=[]
def deps_ok(m):
    if m.endswith('/All'):
        b=m[:-4]; return all(os.path.exists(f"/tmp/lc/{b}/Cells{j}.olean") for j in range(1,5))
    return True
while (todo or run):
    run=[(m,p) for m,p in run if p.poll() is None or done.append((m,p.returncode))]
    if len(run)<2 and todo and time.time()-t0<20:
        for m in todo:
            if deps_ok(m):
                todo.remove(m); run.append((m,subprocess.Popen(['bash','build.sh',m]))); break
        else:
            if not run: break
    elif not run and (not todo or time.time()-t0>=20): break
    time.sleep(0.5)
print('done',done,'remaining',len(todo),'elapsed',int(time.time()-t0))
