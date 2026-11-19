"""Exhaustive plane triangulations of the ten-cycle with three inner vertices."""
import argparse
from collections import Counter, defaultdict
from functools import cache
from hashlib import sha256
from itertools import combinations, permutations
import json
from pathlib import Path

from verify_b14_core_marks import K, independent

PATTERNS=tuple(p for n in range(1,K//2+1) for p in combinations(range(K),n) if independent(p))
INNER=(K,K+1,K+2)
PERMUTATIONS=tuple(permutations(INNER))


def edge(a,b):
    return (a,b) if a<b else (b,a)


def cyclic_edges(face):
    return zip(face,face[1:]+face[:1])


def validate(faces):
    edges=Counter(edge(a,b) for f in faces for a,b in cyclic_edges(f))
    boundary={edge(i,(i+1)%K) for i in range(K)}
    if len(faces)!=14 or len(set(faces))!=14 or len(edges)!=26:
        raise ValueError("wrong face or edge count")
    if set(i for f in faces for i in f)!=set(range(K+3)):
        raise ValueError("vertex missing from the triangulation")
    if {e for e,n in edges.items() if n==1}!=boundary or any(n not in (1,2) for n in edges.values()):
        raise ValueError("incorrect edge incidence")
    links=[defaultdict(set) for _ in range(K+3)]
    for a,b,c in faces:
        for x,y,z in ((a,b,c),(b,c,a),(c,a,b)):
            links[x][y].add(z)
            links[x][z].add(y)
    for a,link in enumerate(links):
        expected={(a-1)%K,(a+1)%K} if a<K else set()
        if {b for b,v in link.items() if len(v)==1}!=expected or any(len(v)>2 for v in link.values()):
            raise ValueError("incorrect degree in a vertex link")
        todo=[next(iter(link))]
        seen=set()
        while todo:
            b=todo.pop()
            if b not in seen:
                seen.add(b)
                todo.extend(link[b]-seen)
        if seen!=set(link):
            raise ValueError("disconnected vertex link")
    # Orient every face across shared edges, then test against the
    # orientation of the fixed outer cycle. Euler characteristic one
    # and the link checks identify a connected orientable disk.
    oriented={}
    for i,f in enumerate(faces):
        for a,b in cyclic_edges(f):
            oriented.setdefault(edge(a,b),[]).append((i,1 if a<b else -1))
    neighbors=defaultdict(list)
    roots=[]
    for e,incident in oriented.items():
        if e in boundary:
            i,sign=incident[0]
            roots.append((i,-sign if e==(0,K-1) else sign))
        else:
            (i,sign),(j,other)=incident
            neighbors[i].append((j,-sign*other))
            neighbors[j].append((i,-sign*other))
    signs={}
    todo=[roots[0]]
    while todo:
        i,s=todo.pop()
        if i in signs:
            if signs[i]!=s:
                raise ValueError("inconsistent face orientations")
        else:
            signs[i]=s
            todo.extend((j,s*p) for j,p in neighbors[i])
    if len(signs)!=len(faces) or any(signs[i]!=s for i,s in roots):
        raise ValueError("incorrect oriented boundary")
    return edges


def compositions(total,length):
    end=total+length-1
    for bars in combinations(range(end),length-1):
        markers=(-1,*bars,end)
        yield tuple(b-a-1 for a,b in zip(markers,markers[1:]))


def distribute(labels,parts):
    for sizes in compositions(len(labels),parts):
        start=0
        groups=[]
        for size in sizes:
            groups.append(labels[start:start+size])
            start+=size
        yield groups


def face(a,b,c):
    return tuple(sorted((a,b,c)))


def fan(boundary,start,length,c):
    k=len(boundary)
    return tuple(face(boundary[(start+i)%k],boundary[(start+i+1)%k],c) for i in range(length))


def connected(boundary,sites):
    k=len(boundary)
    n=len(sites)
    if n==1:
        yield fan(boundary,0,k,sites[0])
        return
    a,b=sites[:2]
    if n==2:
        for start in range(k):
            for run in range(1,k):
                end=(start+run)%k
                yield (fan(boundary,start,run,a)+fan(boundary,end,k-run,b)
                       +(face(boundary[start],a,b),face(boundary[end],a,b)))
        return
    c=sites[2]
    # Three interior edges bound an interior triangle. A run may have
    # zero edges when two of the three transitions use the same vertex.
    # A three-cycle of interior sites can also enclose a triangular
    # region with one boundary corner when only two sites carry runs.
    for start in range(k):
        for x,y,z in compositions(k,3):
            if sum(v==0 for v in (x,y,z))>=2:
                continue
            l=(start+x)%k
            m=(l+y)%k
            yield (fan(boundary,start,x,a)+fan(boundary,l,y,b)+fan(boundary,m,z,c)
                   +(face(boundary[start],c,a),face(boundary[l],a,b),
                     face(boundary[m],b,c),face(a,b,c)))
    # Start with a connected two-site fill and put the third site in
    # either transition triangle. This covers one interior vertex
    # nested behind a triangle through the other two and one corner.
    for f in connected(boundary,sites[:2]):
        for i,t in enumerate(f):
            if a not in t or b not in t:
                continue
            yield f[:i]+f[i+1:]+tuple(face(u,v,c) for u,v in cyclic_edges(t))
    # Three vertices joined by a path. Each path endpoint has a nonempty
    # boundary run. The middle vertex can touch a run only at a corner.
    for start in range(k):
        for x,z,p,q in compositions(k-2,4):
            x+=1
            z+=1
            l=(start+x)%k
            m=(l+p)%k
            r=(m+z)%k
            yield (fan(boundary,start,x,a)+fan(boundary,l,p,b)
                   +fan(boundary,m,z,c)+fan(boundary,r,q,b)
                   +(face(boundary[start],a,b),face(boundary[l],a,b),
                     face(boundary[m],b,c),face(boundary[r],b,c)))


@cache
def triangle(boundary,sites):
    if not sites:
        return ((face(*boundary),),)
    # There are no interior boundary chords. The inner graph is
    # connected because distinct components require a separating chord.
    return tuple(connected(boundary,sites))


def canonical(faces):
    return min(tuple(sorted(face(*(p[i-K] if i>=K else i for i in f)) for f in faces))
               for p in PERMUTATIONS)


def triangulations():
    for skipped in ((),*PATTERNS):
        ear_cycles=tuple(((i-1)%K,i,(i+1)%K) for i in skipped)
        middle=tuple(i for i in range(K) if i not in skipped)
        for assigned in distribute(INNER,len(skipped)+1):
            middle_sites=assigned[-1]
            # The middle cycle has at least five vertices. Any further
            # boundary chord would already appear in this chord set.
            if not middle_sites:
                continue
            variants=[()]
            for boundary,sites in zip(ear_cycles,assigned):
                variants=[a+b for a in variants for b in triangle(boundary,sites)]
            for f in connected(middle,middle_sites):
                for ears in variants:
                    yield tuple(sorted(f+ears)),skipped


def verify():
    tested=set()
    result={}
    tally=Counter()
    for raw,skipped in triangulations():
        faces=canonical(raw)
        if faces in tested:
            continue
        tested.add(faces)
        incidences=validate(faces)
        chords={edge((i-1)%K,(i+1)%K) for i in skipped}
        actual={e for e in incidences if e[1]<K and (e[1]-e[0])%K not in (1,K-1)}
        if chords!=actual:
            raise ValueError("incorrect core chord signature")
        edge_count=sum(i>=K for i,j in incidences)
        tally[len(skipped),edge_count]+=1
        result[faces]=(len(skipped),edge_count)
    rows=[[list(f) for f in faces] for faces in sorted(result)]
    print(f"PASS B=14: {len(rows)} core triangulations modulo permutations of three interior labels.")
    for (n,m),count in sorted(tally.items()):
        print(f"{n} core chords, {m} edges between enclosed centers: {count}")
    print("Face-list SHA-256",sha256(json.dumps(rows,separators=(",",":")).encode()).hexdigest())
    return {"core_boundary_vertices":K,"enclosed_vertices":3,
            "counts":[[n,m,v] for (n,m),v in sorted(tally.items())],"triangulations":rows}


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output",type=Path)
    a=p.parse_args()
    report=verify()
    if a.output:
        a.output.write_text(json.dumps(report,separators=(",",":"))+"\n",encoding="utf-8")
