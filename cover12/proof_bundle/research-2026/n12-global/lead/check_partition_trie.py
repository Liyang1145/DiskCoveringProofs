"""Independent exact prefix-code verification of closed dyadic box partitions.
No producer helpers imported. Does not validate leaf mathematical predicates.
Run: py -3 -B .../check_partition_trie.py MANIFEST OUTPUT
"""
import json,sys,hashlib
from pathlib import Path
from fractions import Fraction as Q

def box(raw):
    assert len(raw)==3
    b=tuple(tuple(Q(v) for v in row) for row in raw)
    assert all(len(row)==2 and row[0]<row[1] for row in b)
    return b

def address(root,target):
    cur=root; bits=[]
    for _ in range(401):
        assert all(a<=c<d<=b for (a,b),(c,d) in zip(cur,target)), 'outside root/child'
        if cur==target:return tuple(bits)
        lens=[b-a for a,b in cur];k=lens.index(max(lens));a,b=cur[k];m=(a+b)/2
        if target[k][1]<=m:side=0;pair=(a,m)
        elif target[k][0]>=m:side=1;pair=(m,b)
        else:raise AssertionError('noncanonical frontier crosses midpoint')
        tmp=list(cur);tmp[k]=pair;cur=tuple(tmp);bits.append(side)
    raise AssertionError('depth exceeds401')

def check(doc):
    root=box(doc['domain']);trie={};frontier=doc['leaves']+[{'H':b,'type':'pending'} for b in doc['pending']]
    kinds={'atomic':0,'infeasible':0,'pending':0};maxdepth=0
    for leaf in frontier:
        kind=leaf['type'];assert kind in kinds,'unknown terminal kind';kinds[kind]+=1
        path=address(root,box(leaf['H']));maxdepth=max(maxdepth,len(path));node=trie
        for bit in path:
            assert 'end' not in node,'descendant of existing frontier leaf'
            node=node.setdefault(bit,{})
        assert not node,'duplicate or ancestor of existing frontier leaf'
        node['end']=kind
    stack=[trie];internal=terminals=0
    while stack:
        node=stack.pop()
        if 'end' in node:
            assert set(node)=={'end'};terminals+=1
        else:
            assert set(node)=={0,1},'incomplete binary prefix code (coverage gap)'
            internal+=1;stack.extend((node[0],node[1]))
    assert terminals==len(frontier) and terminals==internal+1
    c=doc['counts'];assert c['split']==internal
    assert c['certified']==kinds['atomic'] and c['infeasible']==kinds['infeasible']
    assert c['processed']==internal+kinds['atomic']+kinds['infeasible']
    return dict(exact_partition=True,proof='complete binary prefix code reconstructed leaf-to-root',counts=kinds,internal=internal,max_depth=maxdepth,global_exclusion=False,note='Partition only; predicates and atomic replay are separate obligations.')

def controls():
    r=[['0','1']]*3
    def doc(ls):return {'domain':r,'leaves':[{'H':v,'type':'atomic'} for v in ls],'pending':[],'counts':{'split':len(ls)-1,'certified':len(ls),'infeasible':0,'processed':2*len(ls)-1}}
    l=[['0','1/2'],['0','1'],['0','1']];h=[['1/2','1'],['0','1'],['0','1']]
    check(doc([l,h]));check(doc([r]))
    bad=[[l],[l,l],[l,h,r],[[['0','2/3'],['0','1'],['0','1']],h]]
    for leaves in bad:
        try:check(doc(leaves))
        except AssertionError:pass
        else:raise AssertionError('negative control admitted')
    return {'positive':2,'negative_rejected':4}

if __name__=='__main__':
    tests=controls();p=Path(sys.argv[1]);raw=p.read_bytes();doc=json.loads(raw)
    U=Q('0.361102963744508672616920293904');expected=((Q(1,20),U),(Q(0),1-U-Q(1,20)),(Q(0),3*U-1))
    assert box(doc['domain'])==expected,'manifest root differs from mathematical k10 chart'
    out=check(doc);out.update(root_matches_k10_chart=True,source=str(p),source_sha256=hashlib.sha256(raw).hexdigest(),controls=tests)
    Path(sys.argv[2]).write_text(json.dumps(out,indent=2),encoding='utf-8');print(json.dumps(out))
