"""Standard-library acceptance of NEW positive kernels and origin alternatives."""
from pathlib import Path
from collections import deque
import hashlib,json,sys,os
from verify_kernels import model_gate,demand

HERE=Path(__file__).resolve().parent;GRID=10**50

def verify(path,edges):
    cert=json.loads(path.read_text());weights=cert['weight_numerators'];owner=cert['origin_owner']
    demand(owner in (16,25) and len(weights)==135 and all(type(w)is int and w>0 for w in weights),'new positive branch weights')
    matrix=[{} for _ in range(76)]
    for (u,v),w in zip(edges,weights):
        for a,b,x in [(u,u,w),(v,v,w),(u,v,-w),(v,u,-w)]:matrix[a][b]=matrix[a].get(b,0)+x
    center=16+owner;matrix[center][center]=matrix[center].get(center,0)+weights[-1]
    V=[[int(x) for x in row] for row in cert['inverse_numerators']];den=int(cert['inverse_denominator'])
    demand(den>0 and len(V)==60 and all(len(row)==60 for row in V),'new exact inverse dimensions')
    demand(all(V[i][j]==V[j][i] for i in range(60) for j in range(60)),'new inverse symmetry')
    for i in range(60):
        row=[(k-16,w) for k,w in matrix[16+i].items() if k>=16]
        for j in range(60):
            demand(sum(w*V[k][j] for k,w in row)==(den if i==j else 0),'new exact inverse identity')
    H=[[sum(-w*V[i][k-16] for k,w in matrix[j].items() if k>=16) for j in range(16)] for i in range(60)]
    demand(all(min(row)>=0 and sum(row)<=den for row in H),'new unit-anchor and zero-origin harmonic weights')
    response=[[matrix[i].get(j,0)*den+sum(w*H[k-16][j] for k,w in matrix[i].items() if k>=16)
               for j in range(16)] for i in range(16)]
    demand(all(response[i][j]==response[j][i] for i in range(16) for j in range(16)),'new response symmetry')
    demand(all(response[i][j]<=0 for i in range(16) for j in range(16) if i!=j),'new positive pair weights')
    origin=[sum(row) for row in response];demand(min(origin)>=0,'positive response to zero-origin anchor')
    denominator=den*sum(weights)
    pairs=[]
    for i in range(16):
        for j in range(i+1,16):
            value=-response[i][j]
            if value:
                low=value*GRID//denominator;high=-((-value*GRID)//denominator)
                pairs.append([i,j,str(low),str(high)])
    constant=sum(origin)*GRID//denominator
    return {'leaf_index':cert['leaf_index'],'origin_owner':owner,'pairs':pairs,
        'constant_lower':str(constant),'coefficient_denominator':str(GRID),
        'reference_turns':cert['reference_turns'],'source_kernel_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'exact_inverse_and_origin_ground_response_checked':True,'conditional_on_this_origin_owner':True}

if __name__=='__main__':
    leaf=int(sys.argv[1]) if len(sys.argv)>1 else 2136
    stage=os.environ.get('N26_STAGE','');stem='leaf-'+str(leaf)+('-'+stage if stage else '')
    model=json.loads((HERE/'RECOVERED-PHYSICAL-GRAPH.json').read_text());edges=model_gate(model)
    adjacency=[set() for _ in range(76)]
    for u,v in edges:adjacency[u].add(v);adjacency[v].add(u)
    dist=[999]*76;queue=deque(range(16))
    for i in range(16):dist[i]=0
    while queue:
        u=queue.popleft()
        for v in adjacency[u]:
            if dist[v]>dist[u]+1:dist[v]=dist[u]+1;queue.append(v)
    possible=[i for i in range(26) if dist[16+i]>3]
    demand(possible==[16,25],'elementary origin-owner dichotomy from three-rod paths')
    results=[]
    for owner in possible:
        path=HERE/'fresh-kernels'/(stem+'-owner-'+str(owner)+'.json')
        results.append(verify(path,edges));print('verified NEW origin kernel',leaf,owner,flush=True)
    out={'leaf_index':leaf,'origin_owner_alternatives':possible,'radius_scope':'r < 1/4',
        'rod_path_lengths_to_centers':dist[16:42],'kernels':results,
        'original_native_payments_changed':False,'global_optimality_proved':False}
    (HERE/'fresh-kernels'/(stem+'-VERIFIED.json')).write_text(json.dumps(out,indent=2)+'\n')
    print('PASS both fresh exact conditional kernels; no closed box excluded yet')
