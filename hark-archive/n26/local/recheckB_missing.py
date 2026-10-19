"""certB independent recheck of close_missing_A pieces. Resumable. usage: recheckB_missing.py budget"""
import sys,os,json,time
sys.path.insert(0,'/workspace/work/dcp-n26/v3replay'); sys.path.insert(0,'/workspace/work/dcp-n26/local')
from fractions import Fraction as F
import prop,certB
D='/workspace/work/dcp-n26/local/'; OUT=D+'recheckB_missing.jsonl'
d=json.load(open(D+'lleaf_boxes_missing.json'))['missing']
done=set()
if os.path.exists(OUT): done={json.loads(l)['leaf'] for l in open(OUT)}
T0=time.time();B=float(sys.argv[1]);n=0
for k in sorted(d,key=int):
    if k in done: continue
    if time.time()-T0>B: break
    rec=json.load(open(D+f'missing_closed/L{k}.json'))
    lo=[F(x) for x in d[k]['lo']];hi=[F(x) for x in d[k]['hi']];ok=rec['closed'];mb=None
    for p in rec['pieces']:
        if 'bound' not in p: ok=False;continue
        ba,bb=F(p['ba']),F(p['bb'])
        try: bd=certB.check_leaf(prop.weight((ba+bb)/2/prop.AA),lo,hi,ba,bb,prop.MU)
        except Exception as e: bd=None
        if bd is None or bd<=0: ok=False
        else: mb=bd if mb is None else min(mb,bd)
    open(OUT,'a').write(json.dumps({'leaf':k,'okB':bool(ok),'minB':None if mb is None else float(mb)})+'\n');n+=1
print(n,len(done)+n,len(d))
