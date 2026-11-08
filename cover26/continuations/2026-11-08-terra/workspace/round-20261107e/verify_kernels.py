"""Fresh integer checks of 29 kernels on an independently specified physical graph."""
from pathlib import Path
from collections import deque
from copy import deepcopy
import hashlib,json

HERE=Path(__file__).resolve().parent
GRID=10**50

def demand(p,message):
    if not p:raise ValueError(message)

def model_gate(model):
    edges=model['edges'];faces=model['faces_by_witness'];mapping={int(i):j for i,j in model['physical_to_independent_cover_labels'].items()}
    demand(len(edges)==134 and len({tuple(sorted(e)) for e in edges})==134,'134 distinct rods')
    demand(sorted(mapping)==sorted(mapping.values())==list(range(26)) and all(mapping[i]==i for i in range(16)),'fixed boundary graph isomorphism')
    target=json.loads((HERE.parent/'round-20261107b/topology.json').read_text())['faces']
    demand({tuple(sorted(mapping[x] for x in f)) for f in faces}=={tuple(sorted(f)) for f in target},'all 34 candidate faces')
    anchors=[set() for _ in range(16)];witnesses=[set() for _ in range(34)]
    adjacency=[set() for _ in range(76)]
    for u,v in edges:
        demand(type(u)is int and type(v)is int and 0<=u<76 and 0<=v<76 and u!=v,'rod endpoint')
        adjacency[u].add(v);adjacency[v].add(u)
        if u<16 and 16<=v<32:anchors[u].add(v-16)
        elif v<16 and 16<=u<32:anchors[v].add(u-16)
        elif 42<=u<76 and 16<=v<42:witnesses[u-42].add(v-16)
        elif 42<=v<76 and 16<=u<42:witnesses[v-42].add(u-16)
        else:raise ValueError('rod outside explicit physical model')
    demand(all(anchors[i]=={i,(i+1)%16} for i in range(16)),'all 32 boundary rods')
    demand([sorted(f) for f in witnesses]==faces,'all 102 face rods')
    seen={0};queue=deque([0])
    while queue:
        for j in adjacency[queue.popleft()]:
            if j not in seen:seen.add(j);queue.append(j)
    demand(len(seen)==76,'positive grounded connectivity')
    return edges

def kernel(edges,certificate):
    weights=certificate['weight_numerators'];scale=certificate['weight_scale']
    demand(type(scale)is int and scale>0 and len(weights)==134 and all(type(w)is int and w>0 for w in weights),'positive physical weights')
    matrix=[{} for _ in range(76)]
    for (u,v),w in zip(edges,weights):
        for a,b,value in [(u,u,w),(v,v,w),(u,v,-w),(v,u,-w)]:matrix[a][b]=matrix[a].get(b,0)+value
    V=[[int(x) for x in row] for row in certificate['inverse_numerators']]
    den=int(certificate['inverse_denominator'])
    demand(den>0 and len(V)==60 and all(len(row)==60 for row in V),'grounded inverse dimensions')
    demand(all(V[i][j]==V[j][i] for i in range(60) for j in range(60)),'inverse symmetry')
    for i in range(60):
        row=[(k-16,w) for k,w in matrix[16+i].items() if k>=16 and w]
        for j in range(60):
            demand(sum(w*V[k][j] for k,w in row)==(den if i==j else 0),'exact grounded inverse')
    H=[[sum(-w*V[i][k-16] for k,w in matrix[j].items() if k>=16)
        for j in range(16)] for i in range(60)]
    demand(all(min(row)>=0 and sum(row)==den for row in H),'exact harmonic convex combinations')
    response=[[matrix[i].get(j,0)*den+sum(w*H[k-16][j] for k,w in matrix[i].items() if k>=16)
               for j in range(16)] for i in range(16)]
    demand(all(sum(row)==0 for row in response),'response row sums')
    demand(all(response[i][j]==response[j][i] for i in range(16) for j in range(16)),'response symmetry')
    demand(all(response[i][j]<=0 for i in range(16) for j in range(16) if i!=j),'positive boundary pair energies')
    total=sum(weights);denominator=den*total;pairs=[]
    for i in range(16):
        for j in range(i+1,16):
            value=-response[i][j]
            if value:
                lo=value*GRID//denominator
                hi=-((-value*GRID)//denominator)
                demand(lo*denominator<=value*GRID<=hi*denominator,'outward normalized response')
                pairs.append([i,j,str(lo),str(hi)])
    return {'pairs':pairs,'coefficient_denominator':str(GRID),'positive_grounded_inverse_checked':True,
        'harmonic_convexity_checked':True,'weight_sum_numerator':str(total),'weight_scale':str(scale)}

def run():
    model=json.loads((HERE/'RECOVERED-PHYSICAL-GRAPH.json').read_text());edges=model_gate(model)
    table=json.loads((HERE/'supports/TABLE.json').read_text());rows=[];first=None
    demand(len(table['supports'])==29,'29-support scope')
    for entry in table['supports']:
        path=HERE/'supports'/entry['file'];raw=path.read_bytes()
        demand(hashlib.sha256(raw).hexdigest()==entry['sha256'],'exact extracted support values')
        data=json.loads(raw)
        if first is None:first=data['kernel_certificate']
        result=kernel(edges,data['kernel_certificate'])
        rows.append({'index':entry['index'],'source_support_sha256':entry['sha256'],**result})
        print('verified exact physical kernel',entry['index'],flush=True)
    rejected=[]
    for name,mutate in [('wrong-inverse',lambda d:d['inverse_numerators'][0].__setitem__(0,str(int(d['inverse_numerators'][0][0])+1))),
                        ('changed-rod-weight',lambda d:d['weight_numerators'].__setitem__(0,d['weight_numerators'][0]+1))]:
        altered=deepcopy(first);mutate(altered)
        try:kernel(edges,altered)
        except ValueError:rejected.append(name)
        else:raise ValueError('corrupted kernel accepted')
    result={'source_snapshot_sha256':table['source_sha256'],'model_sha256':hashlib.sha256((HERE/'RECOVERED-PHYSICAL-GRAPH.json').read_bytes()).hexdigest(),
        'kernels':rows,'rejected_controls':rejected,'exact_kernel_identities_verified':True,
        'old_model_anchor_orientation_identity_assumed':False,'original_geometry_joint_acceptance':False,
        'new_closed_leaf_payments':0,'global_optimality_proved':False}
    (HERE/'KERNELS-VERIFIED.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS all 29 exact grounded kernels; no old history or geometry acceptance')

if __name__=='__main__':run()
