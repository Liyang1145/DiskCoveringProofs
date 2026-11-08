"""Independent controls for the supplied n=14 package; preserves source bytes."""
from pathlib import Path
from fractions import Fraction as Q
from copy import deepcopy
from contextlib import redirect_stdout
from math import factorial
import gzip, hashlib, io, json, subprocess, sys, tempfile

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'extracted/N=14'
sys.path.insert(0,str(SOURCE))
import network
from interval import Interval as I, PI, SCALE

def demand(ok, message):
    if not ok: raise ValueError(message)

def atan_bounds(x, count):
    total=sum(((-1)**k*x**(2*k+1)/Q(2*k+1) for k in range(count)), Q(0))
    next_term=(-1)**count*x**(2*count+1)/Q(2*count+1)
    return min(total,total+next_term),max(total,total+next_term)

def trig_bounds(x, sine):
    count=100
    power=1 if sine else 0
    total=sum(((-1)**k*x**(2*k+power)/factorial(2*k+power) for k in range(count)),Q(0))
    error=abs(x)**(2*count+power)/factorial(2*count+power)
    return total-error,total+error

def main():
    demand(__debug__,'assertions required')
    inputs={p.relative_to(HERE).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
            for p in SOURCE.iterdir() if p.is_file()}
    a,b=atan_bounds(Q(1,5),120);c,d=atan_bounds(Q(1,239),40)
    independent_pi=(16*a-4*d,16*b-4*c)
    demand(Q(PI.lo,SCALE)<=independent_pi[0]<=independent_pi[1]<=Q(PI.hi,SCALE),'independent Machin pi enclosure')
    for x in map(Q,['0','.1','1','2','4','6']):
        xx=I(x);co,si=network.unit_at(xx.lo,xx.hi)
        for got,sine in [(co,False),(si,True)]:
            lo,hi=trig_bounds(x,sine)
            demand(Q(got.lo,SCALE)<=lo<=hi<=Q(got.hi,SCALE),'independent rational trigonometry')
    payload=json.loads(gzip.decompress((SOURCE/'cover-proof.json.gz').read_bytes()))
    sections=payload if isinstance(payload,list) else [payload]
    counts={}
    for section in sections:
        n=section['n'];cases=list(network.representatives(n));kinds={}
        def walk(node):
            tag=node[0] if node else 'open';kinds[tag]=kinds.get(tag,0)+1
            if tag=='s':walk(node[3]);walk(node[4])
        for _,tree in section['entries']:walk(tree)
        demand(sorted(j for j,_ in section['entries'])==list(range(len(cases))),'complete representative inventory')
        counts[str(n)]={'representatives':len(cases),'tree_node_kinds':kinds}
    section=sections[0];n=section['n'];r=I(section['r']);cases=list(network.representatives(n))
    rejected=[]
    def reject(name,fun):
        try:fun()
        except (AssertionError,ValueError,RuntimeError):rejected.append(name)
        else:raise ValueError('corruption accepted: '+name)
    def first_force(node):
        if node[0]=='f':return node
        if node[0]=='s':return first_force(node[3]) or first_force(node[4])
        return None
    for j,tree in section['entries']:
        force=first_force(tree)
        if force:
            bad=deepcopy(force);bad[1][0][0]+=1
            cuts,edges=network.graph(n,cases[j][1])
            root=network.interval_box(tuple((0,network.GRID) for _ in range(n-1)))
            reject('unbalanced-force',lambda:network.force_margin(n,cases[j][1],r,root,bad[1:]))
            break
    from neighborhood import near_checker
    split_index,split=next((j,tree) for j,tree in section['entries'] if tree[0]=='s')
    bad=deepcopy(split);bad[3]=[]
    demand(network.check_tree(n,cases[split_index][1],r,bad,near_checker(n,cases[split_index][1],r))['open']>=1,'a dropped closed child stays OPEN')
    rejected.append('dropped-child-not-accepted-as-complete')
    for j,_ in section['entries']:
        near=near_checker(n,cases[j][1],r)
        if near:
            reject('whole-domain-fake-near-leaf',lambda:network.check_tree(n,cases[j][1],r,['n'],near))
            break
    altered=deepcopy(sections);altered[0]['entries']=altered[0]['entries'][1:]
    with tempfile.TemporaryDirectory(prefix='negative-',dir=HERE) as tmp:
        path=Path(tmp)/'missing-representative.json.gz'
        path.write_bytes(gzip.compress(json.dumps(altered).encode()))
        with redirect_stdout(io.StringIO()):
            reject('omitted-representative',lambda:network.check_files([path],require_complete=True))
    result=subprocess.run([sys.executable,'-B','-O',str(SOURCE/'verify.py')],capture_output=True,text=True)
    demand(result.returncode!=0 and 'assertions enabled' in result.stderr,'python -O must reject')
    rejected.append('assertions-disabled')
    demand(len(rejected)==5,'all five negative controls executed')
    demand(all(hashlib.sha256((HERE/p).read_bytes()).hexdigest()==h for p,h in inputs.items()),'supplied source bytes unchanged')
    report={'scope':'supplied n14 package arithmetic replay and corruption controls; analytic reduction separately reviewed',
            'input_sha256':inputs,'independent_pi_and_trig_checks':True,'inventory':counts,'negative_controls_rejected':rejected,
            'source_bytes_unchanged':True,'new_unrestricted_theorem_adoption':False,'n26_payments':0}
    (HERE/'CONTROLS.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2,ensure_ascii=False))

if __name__=='__main__':main()
