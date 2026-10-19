import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_MAIN_REPO
import json,os,hashlib,copy
import lgeom
P=json.load(open(DCP_MAIN_REPO+'/cover26/proof_bundle/work/n26-sharp-candidate-angles-proposal-v3.json'))
nodes=copy.deepcopy(P['nodes'])
TF=['97','98','99','100','136','176','289','290','296','308']
TL=['135','175','295','304','28']
if os.path.exists('open23_assembled.json'): TL+=json.load(open('open23_assembled.json'))
def sha(p): return hashlib.sha256(open(p,'rb').read()).hexdigest()
def graft(root_idx,sub):
    """sub: list of nodes with local child indices; node 0 goes to root_idx."""
    base=len(nodes); mp={0:root_idx}
    for i in range(1,len(sub)): mp[i]=base+i-1
    nodes.extend([None]*(len(sub)-1))
    for i,n in enumerate(sub):
        n=copy.deepcopy(n)
        if n['kind']=='SPLIT': n['children']=[mp[c] for c in n['children']]
        nodes[mp[i]]=n
for t in TF:
    st=json.load(open(f'subtrees/{t}.json')); assert st['done'] and all(st['nodes'])
    assert nodes[int(t)]=={'kind':'OPEN'}; graft(int(t),st['nodes'])
for t in TL:
    tr,sl=lgeom.tree(t)
    flat=[]
    def fl(n):
        i=len(flat); flat.append(None)
        if n['kind']=='SPLIT':
            c0=fl(n['children'][0]); c1=fl(n['children'][1])
            flat[i]={'kind':'SPLIT','axis':n['axis'],'mid':n['mid'],'children':[c0,c1]}
        else:
            k=n['n']; m=sl[k][0]
            flat[i]={'kind':'_SLAB','n':k,'m':m}
        return i
    fl(tr)
    # expand slabs
    sub=[]
    # first copy flat, then replace _SLAB by either LOCAL-SLAB or force subtree graft
    assert nodes[int(t)]=={'kind':'OPEN'}
    base=len(nodes); mp={0:int(t)}
    for i in range(1,len(flat)): mp[i]=base+i-1
    nodes.extend([None]*(len(flat)-1))
    for i,n in enumerate(flat):
        if n['kind']=='SPLIT':
            nodes[mp[i]]={'kind':'SPLIT','axis':n['axis'],'mid':n['mid'],'children':[mp[c] for c in n['children']]}
        elif n['m']>=0:
            f=f'lleaves/{t}/s{n["n"]}.json'
            if not os.path.exists(f):
                import shgeom; m_,lo_,hi_=sl[n['n']]; sh=shgeom.map_slab(m_,lo_,hi_); assert sh is not None,(t,n)
                f=f'lleaves/shared/m{m_}_s{sh}.json'; assert json.load(open(f))['closed']
            nodes[mp[i]]={'kind':'LOCAL-SLAB','file':'v3replay/'+f,'sha256':sha(f)}
        else:
            st=json.load(open(f'fleaves/{t}_s{n["n"]}.json')); assert st['done'] and all(st['nodes'])
            graft(mp[i],st['nodes'])
assert all(n is not None for n in nodes)
from collections import Counter
c=Counter(n['kind'] for n in nodes); print(c)
out={'schema':'N26-v3-replay-extension-proposal-ARITHMETIC-ONLY','base':'repo/cover26/proof_bundle/work/n26-sharp-candidate-angles-proposal-v3.json',
     'base_sha256':sha(DCP_MAIN_REPO+'/cover26/proof_bundle/work/n26-sharp-candidate-angles-proposal-v3.json'),
     'closed_targets':TF+TL,'spec':P['spec'],'nodes':nodes,
     'note':'LOCAL-SLAB is NOT an archive-accepted leaf kind (134-rod Schur-energy 2nd-order local cert, needs interface lemma). FORCE leaves use archive direct-arc force_check. Radius compared to RSTAR_UP 0.234700090400448239616790133776692127560495963654971391785925 (not the stress VERIFIED.json endpoint, which is not public).'}
json.dump(out,open('V3-REPLAY-TREE.json.tmp','w')); os.replace('V3-REPLAY-TREE.json.tmp','V3-REPLAY-TREE.json')
print(len(nodes), sha('V3-REPLAY-TREE.json'))
