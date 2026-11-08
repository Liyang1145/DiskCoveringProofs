"""Reconstruct sharp angular constraints and every closed tree domain exactly."""
from pathlib import Path
from fractions import Fraction as Q
from collections import deque
import json,sys,math

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'round-20261107d/native-source'))
import exact_arcs as arcs
SCALE=10**40
RADIUS=Q('0.234700090400448239616790133776692127560495963654971391785925')

def demand(p,message):
    if not p:raise ValueError(message)

def caps():
    out=[]
    for k in range(1,5):
        lo,hi=0,SCALE//2
        while hi-lo>1:
            mid=(lo+hi)//2
            lower=Q(arcs.sincos_turn(Q(mid,2*SCALE))[1][0],arcs.SCALE)
            if lower>k*RADIUS:hi=mid
            else:lo=mid
        demand(Q(arcs.sincos_turn(Q(hi,2*SCALE))[1][0],arcs.SCALE)>k*RADIUS,'sharp cap sine margin')
        out.append(hi)
    return out

def matrix_from_graph(faces,cap):
    adjacent=[set() for _ in range(26)]
    for face in faces:
        for v in face:adjacent[v].update(x for x in face if x!=v)
    distances=[]
    for start in range(26):
        d=[99]*26;d[start]=0;queue=deque([start])
        while queue:
            v=queue.popleft()
            for w in adjacent[v]:
                if d[w]>d[v]+1:d[w]=d[v]+1;queue.append(w)
        distances.append(d)
    bounds={}
    def edge(i,j,c):bounds[i,j]=min(bounds.get((i,j),2*SCALE),c)
    for i in range(16):
        j=(i+1)%16;edge(i,j,cap[0]-(SCALE if j==0 else 0));edge(j,i,SCALE if j==0 else 0)
    for i in range(16):
        for j in range(i+1,16):
            h=min(distances[u][v] for u in (i,(i+1)%16) for v in (j,(j+1)%16))
            if h>3:continue
            width=j-i;bound=cap[h]
            if min(width,16-width)*cap[0]<=bound:continue
            forward=width*cap[0]<SCALE-bound;backward=(16-width)*cap[0]<SCALE-bound
            demand(not(forward and backward),'consistent directed anchor arc')
            if forward:edge(i,j,bound)
            if backward:edge(j,i,bound-SCALE)
    direct=[(i,j,c) for (i,j),c in sorted(bounds.items())]
    infinity=10*SCALE
    floyd=[[0 if i==j else bounds.get((i,j),infinity) for j in range(16)] for i in range(16)]
    for k in range(16):
        for i in range(16):
            for j in range(16):floyd[i][j]=min(floyd[i][j],floyd[i][k]+floyd[k][j])
    demand(all(floyd[i][i]==0 for i in range(16)),'no negative angle cycle')
    for start in range(16):
        row=[infinity]*16;row[start]=0
        for _ in range(15):
            before=row.copy()
            for i,j,c in reversed(direct):row[j]=min(row[j],row[i]+c)
            if row==before:break
        demand(row==floyd[start],'BFS/Bellman and Floyd angular closure agree')
    return floyd,direct

def contract(matrix,lower,upper):
    low=[Q(0),*lower];high=[Q(0),*upper]
    a=[max(low[i]-Q(matrix[j][i],SCALE) for i in range(16)) for j in range(16)]
    b=[min(high[i]+Q(matrix[i][j],SCALE) for i in range(16)) for j in range(16)]
    if any(x>y for x,y in zip(a,b)):return None
    demand(a[0]==b[0]==0,'fixed rotation gauge')
    return a[1:],b[1:]

def all_domains(data,matrix):
    row=data['actual_source_closed_box'];nodes=data['nodes']
    queue=deque([(0,list(map(Q,row['sharp_lower'])),list(map(Q,row['sharp_upper'])))])
    result={};parents={}
    while queue:
        index,lower,upper=queue.popleft()
        demand(type(index)is int and 0<=index<len(nodes) and index not in result,'tree reachability and unique ownership')
        box=contract(matrix,lower,upper);result[index]=box;node=nodes[index]
        if box is None:
            demand(node=={'kind':'EMPTY'},'empty-domain classification');continue
        if node['kind']!='SPLIT':continue
        lo,hi=box;axis=node['axis'];cut=Q(node['mid']);children=node['children']
        demand(type(axis)is int and 0<=axis<15 and lo[axis]<cut<hi[axis],'strict interior split cut')
        demand(len(children)==2 and children[0]!=children[1],'both distinct closed children')
        for side,child in enumerate(children):
            demand(child not in parents and child!=0,'no duplicated child or lost parent')
            parents[child]=index;a,b=lo.copy(),hi.copy()
            if side==0:b[axis]=cut
            else:a[axis]=cut
            queue.append((child,a,b))
    demand(set(result)==set(range(len(nodes))),'all 2999 nodes reachable')
    return result,parents

def run():
    data=json.loads((HERE/'arithmetic-working-projection.json').read_text())
    graph=json.loads((HERE/'RECOVERED-PHYSICAL-GRAPH.json').read_text())
    cap=caps();print('sharp caps',cap,flush=True)
    matrix,direct=matrix_from_graph(graph['faces_by_witness'],cap)
    domains,parents=all_domains(data,matrix)
    actual=[];mismatches=[]
    for leaf in data['pending_closed_leaf_boxes']:
        index=leaf['index'];box=domains[index]
        expected=list(map(Q,leaf['lower'])),list(map(Q,leaf['upper']))
        if box!=expected:mismatches.append(index)
        actual.append({'index':index,'kind':'OPEN','lower':list(map(str,box[0])),'upper':list(map(str,box[1]))})
    print('reconstructed nodes',len(domains),'OPEN count',len(actual),'mismatched boxes',len(mismatches),mismatches[:20],flush=True)
    result={'sharp_caps':list(map(str,cap)),'scale':str(SCALE),'radius_upper':str(RADIUS),
        'matrix':[[str(x) for x in row] for row in matrix],'direct_edges':[[i,j,str(c)] for i,j,c in direct],
        'all_nodes_reconstructed':len(domains),'open_count':len(actual),'mismatches':mismatches,
        'pending_closed_leaf_boxes':actual,'original_arithmetic_acceptance_replayed':False,
        'new_geometric_payments':0}
    (HERE/'DOMAIN-RECONSTRUCTION.json').write_text(json.dumps(result,indent=2)+'\n')
    demand(not mismatches,'Fresh sharp domain reconstruction differs from original source')
    print('PASS: all 344 actual closed OPEN domains match exact reconstruction')

if __name__=='__main__':run()
