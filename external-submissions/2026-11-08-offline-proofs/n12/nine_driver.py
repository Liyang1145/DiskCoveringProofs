"""Offline coverage of the inner-center domain for nine boundary disks."""

import argparse
from bisect import bisect_left
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
import ctypes as ct
import gzip
from itertools import count
import json
from math import isqrt
import os
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory
from time import monotonic

from ten_driver import S, K, ROOT_DIR, square_min, split


R = 397036907462
D = 739421569679
T = D - R
MINIMUM = 205388772068  # round down 0.1868 * S
MAXIMUM = S - R
ROOT = ((MINIMUM, MAXIMUM), (-MAXIMUM, R-T), (0, R), (-MAXIMUM, MAXIMUM), (-MAXIMUM, MAXIMUM))
LIB = None
SEARCH = None
CACHED_MEASURES=[]
WARM=None
POINT = ct.c_int64 * 6
BOUNDS = ct.c_int64 * 10
WEIGHTS = ct.c_int64 * (4*K)
OUT = ct.c_int64 * 3
MASK = ct.c_int64 * 33
EXTRA_MASK = ct.c_int64 * 84


def sample_central():
    """Rational directions, with exact dyadic points in the central disk."""
    out = [(T, 0), (-T, 0), (0, T), (0, -T)]
    for j in range(1, 10):
        x = (T-2)*(100-j*j)//(100+j*j)
        y = (T-2)*(20*j)//(100+j*j)
        for _ in range(4):
            out.append((x, y))
            x, y = -y, x
    return out


CENTRAL = sample_central()
if any(x*x+y*y>T*T for x,y in CENTRAL):
    raise ArithmeticError('central sample outside the certified central disk')


def contract_reference(box):
    """Intersect with elementary necessary conditions. Every candidate is retained."""
    old = list(box)
    z = (0, 0)
    for _ in range(2):
        s0, s1 = old[0]
        for j in (1, 3):
            sx, sy = old[j], old[j+1]
            min_norm = square_min(*sx) + square_min(*sy)
            if min_norm > s1*s1:
                return None
            s0 = max(s0, isqrt(min_norm))
            for index in (j, j+1):
                a, b = old[index]
                old[index] = (max(a,-s1), min(b,s1))
        old[0] = (s0, s1)
        if any(a>b for a,b in old):
            return None

        def restrict(k, x, y):
            if k == 0:
                gap = R*R-y*y
                if gap < 0:
                    return False
                h = isqrt(gap)+1
                old[0] = (max(old[0][0],x-h), min(old[0][1],x+h))
                return old[0][0] <= old[0][1]
            a, b = old[k]
            c, d = old[k+1]
            gap_x = R*R-square_min(c-y,d-y)
            gap_y = R*R-square_min(a-x,b-x)
            if min(gap_x,gap_y)<0:
                return False
            hx, hy = isqrt(gap_x)+1, isqrt(gap_y)+1
            old[k] = (max(a,x-hx),min(b,x+hx))
            old[k+1] = (max(c,y-hy),min(d,y+hy))
            return old[k][0] <= old[k][1] and old[k+1][0] <= old[k+1][1]

        if not restrict(1,-T,0):
            return None
        for x,y in CENTRAL:
            possible = []
            for k in (0,1,3):
                a,b = old[k]
                c,d = z if k == 0 else old[k+1]
                if square_min(a-x,b-x)+square_min(c-y,d-y) <= R*R:
                    possible.append(k)
            if not possible:
                return None
            if len(possible)==1 and not restrict(possible[0],x,y):
                return None
    return tuple(old)


def contract(box):
    buf=BOUNDS(*(v for row in box for v in row))
    status=load_library().contract_nine(buf)
    if status==0:
        return None
    if status!=1:
        raise ArithmeticError('contraction failed')
    return tuple((buf[2*k],buf[2*k+1]) for k in range(5))


def load_library():
    global LIB
    if LIB is not None:
        return LIB
    LIB = ct.CDLL(str(ROOT_DIR/os.environ.get('N12_INTERVAL_DLL','ten_intervals.dll')))
    ptr = ct.POINTER(ct.c_int64)
    for name, args in [('get_masks', [ptr,ct.c_int64,ptr]),
                       ('contract_nine', [ptr]),
                       ('get_extra_masks', [ptr,ct.c_int64,ptr]),
                       ('check_nine', [ptr,ct.c_int64,ptr,ct.c_int64,ptr]),
                       ('check_nine_extra', [ptr,ct.c_int64,ptr,ct.c_int64,ptr]),
                       ('check_nine_polar', [ptr,ct.c_int64,ptr,ct.c_int64,ptr,ct.c_int]),
                       ('witness_obstruction', [ptr,ct.c_int64]), ('nine_shape', [ptr]),
                       ('matching_obstruction', [ptr,ct.c_int64,ct.c_int64]),
                       ('check_tangent', [ct.c_int64,ptr])]:
        fun = getattr(LIB,name)
        fun.argtypes = args
        fun.restype = ct.c_int
    dp=ct.POINTER(ct.c_double)
    LIB.search_matrix.argtypes=[dp,ct.c_int,dp,dp,ct.c_int,ct.c_int,ct.c_double,dp]
    LIB.search_matrix.restype=None
    return LIB


def representative(box):
    mid = [(a+b)//2 for a,b in box]
    half = [b-c for (_,b),c in zip(box,mid)]
    high = max(half[0]**2,half[1]**2+half[2]**2,half[3]**2+half[4]**2)
    delta = isqrt(high)
    delta += delta**2 < high
    return POINT(mid[0],0,*mid[1:]), R+delta


def check(box, weights, limit=180000, replay=False):
    if len(weights) not in (4*K,11*K) or any(type(w) is not int or not 0 <= w <= 50000000 for w in weights):
        raise ValueError('invalid weights')
    out = OUT()
    lib = load_library()
    arguments=(*representative(box),(ct.c_int64*len(weights))(*weights),limit,out)
    if os.environ.get('N12_POLAR')=='1':
        status=lib.check_nine_polar(*arguments,int(len(weights)==11*K))
        if status==1 or (status==0 and not replay):
            return status,tuple(out)
    test = lib.check_nine if len(weights)==4*K else lib.check_nine_extra
    status = test(*arguments)
    return status,tuple(out)


def rank_excluded(box):
    # The normalized I1 is a closest center to (-T,0) among I1 and I2.
    _, (a,b), (c,d), (e,f), (g,h) = box
    return (square_min(a+T,b+T)+square_min(c,d) >
            max((e+T)**2,(f+T)**2)+max(g*g,h*h))


def prepare_search():
    global SEARCH
    if SEARCH is None:
        os.environ['OPENBLAS_NUM_THREADS'] = '1'
        import numpy as np
        import ten_search as ts
        d = np.linspace(D/S, 1., 39)
        t = np.arange(144)*np.pi/72
        samples = (d[:,None]*np.exp(1j*t[None,:])).ravel()
        rows = np.arange(samples.size).reshape(len(d),len(t))[::3,::2].ravel()
        SEARCH = np,ts,samples,rows
    return SEARCH


def warm_weights(box):
    global WARM
    file=os.environ.get('N12_WARM_LIBRARY')
    if not file:
        return []
    if WARM is None:
        np,*_=prepare_search()
        from scipy.spatial import cKDTree
        with np.load(file) as data:
            WARM=cKDTree(data['position']),data['weight']
    tree,w=WARM
    distances,indices=tree.query([(a+b)/(2*S) for a,b in box],k=2)
    return [w[i].tolist() for d,i in zip(distances,indices) if d<.023]


def search(box, trial_limit=8, extra=False, strong=False):
    centers,rho = representative(box)
    if rho-R > S//25:
        return None,0
    mask = MASK()
    if load_library().get_masks(centers,rho,mask)!=1:
        return None,0
    np,ts,samples,rows = prepare_search()
    parts = [[(-.5,.5)]]
    for i in range(3):
        inner = []
        for j in range(mask[11*i]):
            inner.append((mask[11*i+2*j+1]/S,mask[11*i+2*j+2]/S))
        parts.append(inner)
    vec = [complex(centers[2*i],centers[2*i+1])/S for i in range(3)]
    ts_radii = [1]+[rho/S]*3
    if extra:
        masks=EXTRA_MASK()
        if load_library().get_extra_masks(centers,rho,masks)!=1:
            return None,0
        for i in range(7):
            ts_radii.append(masks[12*i]/S)
            vec.append(0)
            clip=[]
            for j in range(masks[12*i+1]):
                clip.append((masks[12*i+2*j+2]/S,masks[12*i+2*j+3]/S))
            parts.append(clip)
    target = 1/9
    width=max(b-a for a,b in box)/S
    disk_radius = R/S+(0 if strong==2 else ((.00055 if width>.004 and not strong else .00015)
                                           if extra else .00037))
    circles=np.array([(a.real,a.imag,t) for a,t in zip([0]+vec,ts_radii)],dtype=float)
    masks=np.zeros((len(parts),5,2),dtype=float)
    for i,p in enumerate(parts):
        if p: masks[i,:len(p),:]=p
    points=np.ascontiguousarray(samples,dtype=np.complex128).view(np.float64)
    pointer=ct.POINTER(ct.c_double)

    def matrix(pts,bins):
        array=np.zeros((len(pts)//2,len(parts)*bins),dtype=float)
        load_library().search_matrix(pts.ctypes.data_as(pointer),len(array),circles.ctypes.data_as(pointer),
                                     masks.ctypes.data_as(pointer),len(parts),bins,disk_radius,
                                     array.ctypes.data_as(pointer))
        return array

    def masses(bins):
        edges=np.linspace(-.5,.5,bins+1)
        lo,hi=edges[:-1],edges[1:]
        return np.concatenate([sum((np.maximum(0,np.minimum(b,hi)-np.maximum(a,lo)) for a,b in p),
                                   np.zeros(bins)) for p in parts])

    def rounded(w):
        return [min(50000000,int(round(a*1_000_000))) for a in w]

    if extra:
        bins=8
        coarse=matrix(points,bins)
        small_mass=masses(bins)
        w,cap=ts.find_measure(coarse[rows],small_mass)
        if w is not None and cap<target-.0003 and (coarse@w).max()<target-.0001:
            w=rounded(np.repeat(w,K//bins))
            status,out=check(box,w,limit=18000)
            if status==1:
                return w,out[2]

    mat=matrix(points,K)
    mass=masses(K)
    rows = np.array(rows)
    for attempt in range(trial_limit):
        w,cap = ts.find_measure(mat[rows],mass)
        if w is None or cap > target-(.000015 if strong==2 else .00018):
            return None,0
        scores = mat@w
        top = np.argpartition(scores,-100)[-100:]
        if scores[top].max()>target-.00033 and attempt+1<trial_limit:
            rows = np.union1d(rows,top)
            continue
        if scores[top].max()>=target:
            return None,0
        w = rounded(w)
        status,out = check(box,w,limit=180000 if strong==2 or width<=.002 else (60000 if strong else 14000))
        if status==1:
            return w,out[2]
        if status==0:
            rows = np.append(np.union1d(rows,top),len(mat))
            mat = np.vstack([mat,matrix(np.array([out[0]/S,out[1]/S],dtype=float),K)])
            continue
        return None,0
    return None,0


def geometric(box):
    box = contract(box)
    if box is None:
        return box,'prune'
    lib = load_library()
    if rank_excluded(box):
        return box,'rank'
    result = lib.nine_shape(BOUNDS(*(x for row in box for x in row)))
    if result in (1,2):
        return box,'shape' if result==1 else 'budget'
    if lib.witness_obstruction(*representative(box))==1:
        return box,'witness'
    if lib.matching_obstruction(*representative(box),box[0][1])==1:
        return box,'matching'
    return box,None


def process(item):
    path,box = item
    box,kind=geometric(box)
    if kind is not None:
        return path,box,kind,0
    # If the midpoint already has a geometric certificate, subdivision is
    # cheaper than trying to find a measure for the enlarged test circles.
    width=max(b-a for a,b in box)
    if os.environ.get('N12_SPARSE_ATTEMPTS')=='1' and width>S//650 and len(path)%3!=2:
        return path,box,None,0
    extra=os.environ.get('N12_EXTRA_ARCS')=='1' and width<S//34
    if os.environ.get('N12_PREFER_SPLIT')=='1' and len(path)<55 and width>S//2500:
        inner = tuple(((a+b)//2,)*2 for a,b in box)
        _,center_kind=geometric(inner)
        if center_kind is not None:
            return path,box,None,0
    if extra:
        for old in CACHED_MEASURES[-2:]+warm_weights(box):
            status,info=check(box,old,10000)
            if status==1:
                return path,box,old,info[2]
        w,cells=search(box,trial_limit=8 if width<=S//170 else 5,extra=True)
        if w:
            CACHED_MEASURES.append(w)
            del CACHED_MEASURES[:-2]
        else:
            w,cells=search(box)
    else:
        w,cells=search(box)
        if not w and extra:
            w,cells=search(box,trial_limit=12,extra=True)
    if not w and extra and os.environ.get('N12_FINE_MEASURES')=='1' and width<S//125:
        w,cells=search(box,trial_limit=16,extra=True,strong=2)
    return path,box,w,cells


def contains_descendant(paths,path):
    i=bisect_left(paths,path)
    return i<len(paths) and paths[i].startswith(path)


def read_paths(file):
    source=gzip.open(file,'rt',encoding='utf-8') if file.suffix=='.gz' else file.open(encoding='utf-8')
    seen=set()
    with source as f:
        for line in f:
            p=json.loads(line)[0]
            if p in seen or set(p)-set('01') or len(p)>90:
                raise ValueError('bad path')
            seen.add(p)
    paths=sorted(seen)
    if any(right.startswith(left) for left,right in zip(paths,paths[1:])):
        raise ValueError('leaf is an ancestor of another leaf')
    return seen,paths


def frontier(file):
    leaves,paths = read_paths(file)
    pending = []
    todo = [('',ROOT)]
    while todo:
        path,box=todo.pop()
        if path in leaves:
            continue
        if not contains_descendant(paths,path):
            pending.append((path,box))
            continue
        box=contract(box)
        if box is None:
            raise ValueError('empty non-leaf '+path)
        todo.extend((path+str(bit),b) for bit,b in enumerate(split(box)))
    return pending


def generate(file,jobs,depth_limit,resume=False):
    pending = frontier(file) if resume else [('',ROOT)]
    counts = {}
    total_cells = 0
    start = monotonic()
    print('starting with',len(pending),'open boxes',flush=True)
    with file.open('a' if resume else 'w',encoding='utf-8') as log, ProcessPoolExecutor(max_workers=jobs) as pool:
        for depth in count():
            if not pending or depth>depth_limit:
                break
            following = []
            for path,box,result,cells in pool.map(process,pending,chunksize=2):
                if result is None:
                    for bit,child in enumerate(split(box)):
                        following.append((path+str(bit),child))
                else:
                    log.write(json.dumps([path,result],separators=(',',':'))+'\n')
                    tag = result if isinstance(result,str) else 'measure'
                    counts[tag] = counts.get(tag,0)+1
                    total_cells += cells
            pending = following
            log.flush()
            print('depth',depth,'remaining',len(pending),counts,'outer boxes',total_cells,
                  'seconds',round(monotonic()-start,1),flush=True)
    if pending:
        with file.with_suffix('.pending.jsonl').open('w',encoding='utf-8') as f:
            for p,b in pending:
                f.write(json.dumps([p,b])+'\n')
        print('INCOMPLETE:',len(pending),'uncovered boxes',flush=True)
        return False
    print('COMPLETE',counts,flush=True)
    return True


def chunk(item):
    root, box, maximum_depth = item
    todo = [(root,box)]
    answers = {}
    stuck = []
    done = cells = 0
    geometry_only=os.environ.get('N12_GEOMETRY_SWEEP')=='1'
    while todo and done < 240:
        path,box = todo.pop()
        defer=False
        if geometry_only:
            box,result=geometric(box)
            c=0
            if result is None:
                width=max(b-a for a,b in box)
                if width<=S//1250:
                    defer=True
                elif width<=S//50:
                    mid=tuple(((a+b)//2,)*2 for a,b in box)
                    _,kind=geometric(mid)
                    defer=kind is None
        else:
            path,box,result,c = process((path,box))
        done += 1
        cells += c
        if result is not None:
            if not isinstance(result,str):
                answers[path]=(result,None)
                continue
            depth=0
            while len(path)>len(root):
                sibling=path[:-1]+('0' if path[-1]=='1' else '1')
                if sibling not in answers or answers[sibling][1] is None:
                    break
                _,other_depth=answers.pop(sibling)
                depth=max(depth,other_depth)+1
                path=path[:-1]
            answers[path]=(['geo',depth] if depth else result,depth)
        elif defer or len(path) >= maximum_depth:
            stuck.append((path,box))
        else:
            todo.extend((path+str(bit),b) for bit,b in enumerate(split(box)))
    return [(p,result) for p,(result,_) in answers.items()],todo,stuck,done,cells


def stream_generate(file,jobs,maximum_depth,resume):
    work=frontier(file) if resume else [('',ROOT)]
    if os.environ.get('N12_WARM_LIBRARY'):
        from random import Random
        Random(20261108).shuffle(work)
    ready=deque(work)
    counters={}
    examined=outer=stalled=0
    start=monotonic()
    last=start
    print('starting with',len(ready),'open boxes',flush=True)
    with file.open('a' if resume else 'w',encoding='utf-8') as log, \
            file.with_suffix('.stalled.jsonl').open('w',encoding='utf-8') as failed, \
            ProcessPoolExecutor(max_workers=jobs) as pool:
        pending=set()
        while ready or pending:
            while ready and len(pending)<jobs:
                p,b=ready.popleft()
                pending.add(pool.submit(chunk,(p,b,maximum_depth)))
            complete,pending=wait(pending,return_when=FIRST_COMPLETED)
            for future in complete:
                answers,left,stuck,done,cells=future.result()
                for path,result in answers:
                    log.write(json.dumps([path,result],separators=(',',':'))+'\n')
                    tag=result if isinstance(result,str) else ('geo' if result[0]=='geo' else 'measure')
                    counters[tag]=counters.get(tag,0)+1
                for p,b in stuck:
                    failed.write(json.dumps([p,b])+'\n')
                stalled+=len(stuck)
                ready.extend(left)
                examined+=done
                outer+=cells
            log.flush()
            failed.flush()
            now=monotonic()
            if now-last>15:
                last=now
                print('examined',examined,'queued subtrees',len(ready)+len(pending),
                      'stalled',stalled,counters,'outer boxes',outer,'seconds',round(now-start,1),flush=True)
    print('INCOMPLETE' if stalled else 'COMPLETE', 'stalled',stalled,counters,'outer boxes',outer,flush=True)
    return stalled==0


def reconstruct(path):
    box=ROOT
    for bit in path:
        box=contract(box)
        if box is None:
            return None
        box=split(box)[int(bit)]
    return box


def geometry_tree(box, depth, max_nodes):
    lib=load_library()
    todo=[(box,depth,True)]
    visited=0
    while todo:
        sub,left,contracted=todo.pop()
        visited+=1
        if visited>max_nodes:
            return False
        if contracted:
            if rank_excluded(sub) or lib.nine_shape(BOUNDS(*(x for row in sub for x in row))) in (1,2) or \
                    lib.witness_obstruction(*representative(sub))==1 or \
                    lib.matching_obstruction(*representative(sub),sub[0][1])==1:
                continue
        else:
            sub,kind=geometric(sub)
            if kind is not None:
                continue
        if not left:
            return False
        todo.extend((child,left-1,False) for child in split(sub))
    return True


def close_ancestor(path):
    box=reconstruct(path)
    if box is None:
        return path,None
    box,kind=geometric(box)
    if kind is not None:
        return path,kind
    if os.environ.get('N12_LOCAL_GEOMETRY')=='1':
        mid=tuple(((a+b)//2,)*2 for a,b in box)
        if geometric(mid)[1] is not None and geometry_tree(box,14,10000):
            return path,['geo',14]
    for w in CACHED_MEASURES[-4:]+warm_weights(box):
        if check(box,w,10000)[0]==1:
            return path,w
    weights,_=search(box,trial_limit=10,extra=True,strong=True)
    if weights is None and os.environ.get('N12_FINE_MEASURES')=='1' and max(b-a for a,b in box)<S//125:
        weights,_=search(box,trial_limit=16,extra=True,strong=2)
    if weights is not None:
        CACHED_MEASURES.append(weights)
        del CACHED_MEASURES[:-4]
    return path,weights


def replace_stalled(file,stalled,output,jobs,prefix,expand=0):
    if stalled is None:
        if not expand:
            targets=sorted({p[:prefix] if prefix else p for p,_ in frontier(file)})
        else:
            todo=[(p,b,expand) for p,b in frontier(file)]
            targets=[]
            while todo:
                p,b,depth=todo.pop()
                b=contract(b)
                if b is None or not depth:
                    targets.append(p)
                else:
                    todo.extend((p+str(bit),child,depth-1) for bit,child in enumerate(split(b)))
            targets.sort()
    else:
        existing,_=read_paths(file)
        with stalled.open(encoding='utf-8') as f:
            keys={p[:prefix] if prefix else p[:-14] for p,_ in map(json.loads,f)}
        targets=sorted(p for p in keys if not any(p[:i] in existing for i in range(len(p)+1)))
    print('attempting ancestor boxes',len(targets),flush=True)
    total_targets=len(targets)
    replacements=set()
    journal=output.with_suffix('.journal.jsonl')
    if journal.exists():
        with journal.open(encoding='utf-8') as prior:
            for line in prior:
                path,_=json.loads(line)
                replacements.add(path)
        targets=[p for p in targets if p not in replacements]
    resumed=len(replacements)
    with ProcessPoolExecutor(max_workers=jobs) as pool, journal.open('a',encoding='utf-8') as stream:
        i=0
        for start in range(0,len(targets),jobs*96):
            for path,result in pool.map(close_ancestor,targets[start:start+jobs*96],chunksize=24):
                i+=1
                if result is not None:
                    replacements.add(path)
                    stream.write(json.dumps([path,result],separators=(',',':'))+'\n')
                if i%500==0:
                    stream.flush()
                    print('closed',len(replacements),'after',i+resumed,'attempts',flush=True)
    paths=sorted(replacements)
    with file.open(encoding='utf-8') as source,output.open('x',encoding='utf-8') as dst:
        for line in source:
            path,_=json.loads(line)
            i=bisect_left(paths,path)
            if (i<len(paths) and path.startswith(paths[i])) or (i>0 and path.startswith(paths[i-1])):
                continue
            dst.write(line)
        with journal.open(encoding='utf-8') as proof:
            for line in proof:
                dst.write(line)
    print('certified ancestor boxes',len(paths),'of',total_targets,flush=True)


def replay_leaf(item):
    path,box,kind = item
    lib = load_library()
    if kind=='rank':
        if not rank_excluded(box):
            raise ValueError('invalid rank '+path)
        return kind,0
    if kind=='witness':
        if lib.witness_obstruction(*representative(box))!=1:
            raise ValueError('invalid witness '+path)
        return 'witness',0
    if kind=='matching':
        if lib.matching_obstruction(*representative(box),box[0][1])!=1:
            raise ValueError('invalid matching '+path)
        return 'matching',0
    if kind in ('shape','budget'):
        if lib.nine_shape(BOUNDS(*(x for row in box for x in row))) not in (1,2):
            raise ValueError('invalid shape or budget '+path)
        return kind,0
    if isinstance(kind,list) and kind and kind[0]=='geo':
        if len(kind)!=2 or type(kind[1]) is not int or not 1<=kind[1]<=64:
            raise ValueError('invalid geometry depth '+path)
        if not geometry_tree(box,kind[1],1<<26):
            raise ValueError('open geometric subtree '+path)
        return 'geo',0
    status,out = check(box,kind,replay=True)
    if status!=1:
        raise ValueError('invalid measure '+path)
    return 'measure',out[2]


def replay(file,jobs):
    os.environ.setdefault('N12_POLAR','1')
    tangent = OUT()
    if load_library().check_tangent(2_000_000,tangent)!=1:
        raise ValueError('the global tangent bound was not certified')
    print('tangent bound:',tangent[0],'local Hessian boxes,',tangent[1],
          'exterior boxes and',tangent[2],'boxes inside the local domain',flush=True)
    if file.suffix=='.gz':
        with TemporaryDirectory(prefix='n12-replay-') as d:
            raw=Path(d)/'certificate.jsonl'
            with gzip.open(file,'rb') as source,raw.open('wb') as destination:
                shutil.copyfileobj(source,destination)
            replay_tree(raw,jobs)
    else:
        replay_tree(file,jobs)


def replay_tree(file,jobs):
    leaves={}
    with file.open('rb') as stream:
        while True:
            offset=stream.tell()
            line=stream.readline()
            if not line:
                break
            p=json.loads(line)[0]
            if p in leaves or set(p)-set('01') or len(p)>90:
                raise ValueError('bad path')
            leaves[p]=offset
    paths=sorted(leaves)
    if any(right.startswith(left) for left,right in zip(paths,paths[1:])):
        raise ValueError('leaf is an ancestor of another leaf')
    print('indexed',len(paths),'proof records',flush=True)
    counts = {'prune':0}
    def checks():
        todo = [('',ROOT)]
        with file.open('rb') as stream:
            while todo:
                path,box = todo.pop()
                box = contract(box)
                if path not in leaves:
                    if not contains_descendant(paths,path) or box is None:
                        raise ValueError('missing leaf '+path)
                    todo.extend((path+str(bit),child) for bit,child in enumerate(split(box)))
                    continue
                stream.seek(leaves.pop(path))
                p,kind=json.loads(stream.readline())
                if p!=path:
                    raise ValueError('certificate changed during replay')
                if kind=='prune':
                    if box is not None:
                        raise ValueError('invalid prune '+path)
                    counts['prune'] += 1
                else:
                    if box is None:
                        raise ValueError('non-prune leaf for empty domain')
                    yield path,box,kind
        if leaves:
            raise ValueError('excess leaves')
    total_cells = 0
    from itertools import islice
    inputs=checks()
    batches=0
    with ProcessPoolExecutor(max_workers=jobs) as pool:
        while batch:=list(islice(inputs,4000)):
            for kind,cells in pool.map(replay_leaf,batch,chunksize=12):
                counts[kind] = counts.get(kind,0)+1
                total_cells += cells
            batches+=1
            if batches%10==0:
                print('replay progress',counts,flush=True)
    print('COMPLETE domain proof',counts,'outer boxes',total_cells,flush=True)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('action',choices=['generate','replay','test','repair'])
    p.add_argument('--jobs',type=int,default=12)
    p.add_argument('--depth',type=int,default=32)
    p.add_argument('--resume',action='store_true')
    p.add_argument('--stream',action='store_true')
    p.add_argument('--file',type=Path,default=ROOT_DIR/'nine_certificate.jsonl')
    p.add_argument('--stalled',type=Path)
    p.add_argument('--output',type=Path)
    p.add_argument('--prefix',type=int)
    p.add_argument('--expand',type=int,default=0)
    args=p.parse_args()
    if args.action=='generate':
        complete = (stream_generate if args.stream else generate)(args.file,args.jobs,args.depth,args.resume)
        if not complete:
            raise SystemExit(1)
    elif args.action=='replay':
        replay(args.file,args.jobs)
    elif args.action=='repair':
        replace_stalled(args.file,args.stalled,args.output,args.jobs,args.prefix,args.expand)
    else:
        from math import cos,sin,radians
        for a,b,c,t,u,width in [(.27824,.27824,.27824,120,240,0),(.27824,.27824,.27824,120,240,2),
                                 (.3,.25,.26,124,235,2),(.25,.23,.22,120,240,10),
                                 (.28,.24,.21,99,245,10),(.43,.19,.22,110,230,20)]:
            mid = [a,b*cos(radians(t)),b*sin(radians(t)),c*cos(radians(u)),c*sin(radians(u))]
            box = tuple((round(x*S)-width*S//2000,round(x*S)+width*S//2000) for x in mid)
            start = monotonic()
            _,_,result,cells = process(('test',box))
            print(a,b,c,t,u,width,result if isinstance(result,str) else bool(result),
                  cells,round(monotonic()-start,3),flush=True)


if __name__=='__main__':
    main()
