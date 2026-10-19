import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N11, DCP_TMP
import os,re,json,sys
root=DCP_N11+'/wip/lean'
mods={}
for dp,dn,fn in os.walk(root):
    if '.lake' in dp: continue
    for f in fn:
        if f.endswith('.lean'):
            p=os.path.join(dp,f); rel=os.path.relpath(p,root)[:-5].replace('/','.')
            mods[rel]=p
def strip(s):
    # remove block comments (nested) and line comments and strings roughly
    out=[];i=0;depth=0;n=len(s)
    while i<n:
        if s.startswith('/-',i): depth+=1;i+=2;continue
        if depth and s.startswith('-/',i): depth-=1;i+=2;continue
        if depth: i+=1;continue
        if s.startswith('--',i):
            j=s.find('\n',i); i=n if j<0 else j; continue
        if s[i]=='"':
            j=i+1
            while j<n and s[j]!='"':
                j+= 2 if s[j]=='\\' else 1
            out.append('""'); i=j+1; continue
        out.append(s[i]); i+=1
    return ''.join(out)
info={}
for m,p in mods.items():
    s=open(p,encoding='utf-8',errors='replace').read(); c=strip(s)
    imps=re.findall(r'^\s*import\s+([\w.]+)',c,re.M)
    info[m]=dict(imports=imps,sorry=len(re.findall(r'\bsorry\b',c)),
        axiom=len(re.findall(r'^\s*(?:private\s+|noncomputable\s+)*axiom\s',c,re.M)),
        native=len(re.findall(r'native_decide|ofReduceBool',c)),
        thms=len(re.findall(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*(?:theorem|lemma)\s',c,re.M)),
        defs=len(re.findall(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:def|abbrev|structure|inductive)\s',c,re.M)),
        bytes=len(s))
def closure(start_imps):
    seen=set();st=list(start_imps)
    while st:
        x=st.pop()
        if x in seen or x not in info: continue
        seen.add(x); st+=info[x]['imports']
    return seen
def rootimps(path):
    c=strip(open(path,encoding='utf-8').read()); return re.findall(r'^\s*import\s+([\w.]+)',c,re.M)
cur=closure(rootimps(root+'/N11Formalization.lean'))
old=closure(rootimps(root+'/N11Formalization.lean.pre-c450pilot-20261014'))
def agg(S): return {k:sum(info[m][k] for m in S) for k in ['sorry','axiom','native','thms','defs','bytes']}
print('modules total',len(info),'own N11Formalization.*',sum(m.startswith('N11Formalization.') for m in info))
print('root direct imports cur/old',len(rootimps(root+'/N11Formalization.lean')),len(rootimps(root+'/N11Formalization.lean.pre-c450pilot-20261014')))
print('closure cur',len(cur),agg(cur)); print('closure old',len(old),agg(old))
print('new in cur',sorted(cur-old)); print('dropped',sorted(old-cur))
ext=set(i for m in cur for i in info[m]['imports'] if i not in info); print('external import roots',sorted(set(e.split('.')[0] for e in ext)))
for m in sorted(cur):
    if info[m]['sorry'] or info[m]['axiom'] or info[m]['native']: print('BAD',m,info[m])
outside=[m for m in info if m not in cur]
print('outside closure',len(outside),agg(outside))
json.dump(dict(info=info,cur=sorted(cur),old=sorted(old)),open((os.makedirs(DCP_TMP+'/ana',exist_ok=True) or DCP_TMP)+'/ana/graph.json','w'))
