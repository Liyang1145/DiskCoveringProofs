"""Infer a graph proposal from one kernel, then accept only exact integer identities.

This creates an independent physical model; it does not assert the unavailable
old SYSTEM.json has been recovered or accept any old arithmetic payment.
"""
from pathlib import Path
from collections import Counter
import hashlib,json
import mpmath as mp

HERE=Path(__file__).resolve().parent
support=json.loads((HERE/'supports/support-00.json').read_text())
cert=support['kernel_certificate'];weights=cert['weight_numerators']
V=[[int(x) for x in row] for row in cert['inverse_numerators']]
den=int(cert['inverse_denominator'])
mp.mp.dps=100
M=mp.matrix([[mp.mpf(V[i][j])/den for j in range(26)] for i in range(26)])
inverse=mp.inverse(M)
faces=[];rows=[];witness_edges=[]
for k in range(26,60):
    lam=mp.matrix([[mp.mpf(V[k][j])/den for j in range(26)]])*inverse
    neighbors=[i for i in range(26) if abs(lam[i])>mp.mpf('1e-50')]
    if len(neighbors)!=3:raise ValueError('Numerical proposal did not find three neighbors')
    impedance=mp.mpf(V[k][k])/den-sum(lam[i]*mp.mpf(V[i][k])/den for i in neighbors)
    degree=1/impedance
    proposed=[int(mp.nint(degree*lam[i])) for i in neighbors]
    if min(proposed)<=0:raise ValueError('Nonpositive proposed edge weight')
    for j in range(60):
        if sum(w*(V[k][j]-V[i][j]) for i,w in zip(neighbors,proposed))!=(den if k==j else 0):
            raise ValueError('Exact witness-row inverse identity failed')
    faces.append(neighbors)
    witness_edges.extend((16+k,16+i,w) for i,w in zip(neighbors,proposed))
print('accepted 34 exact witness rows',flush=True)

incident=[[] for _ in range(26)]
for witness,center,w in witness_edges:incident[center-16].append((witness-16,w))
anchor_sums=[]
for i in range(26):
    numerator=den+sum(w*V[k][i] for k,w in incident[i])
    diag,remainder=divmod(numerator,V[i][i])
    if remainder:raise ValueError('Nonintegral proposed diagonal')
    for j in range(60):
        if diag*V[i][j]-sum(w*V[k][j] for k,w in incident[i])!=(den if i==j else 0):
            raise ValueError('Exact center-row inverse identity failed')
    residual=diag-sum(w for _,w in incident[i])
    if (i<16 and residual<=0) or (i>=16 and residual!=0):raise ValueError('Anchor budget changed')
    anchor_sums.append(residual)

remaining=Counter(weights)
for _,_,w in witness_edges:remaining[w]-=1
if any(n<0 for n in remaining.values()) or sum(remaining.values())!=32:
    raise ValueError('Witness weights do not retain complete 134-weight multiset')
unused=[]
for i,w in enumerate(weights):
    if remaining[w]>0:unused.append(i);remaining[w]-=1
boundary=None;anchor_order=None
for order,reverse in [('anchor-pairs',False),('anchor-pairs',True),('center-pairs',False),('center-pairs',True)]:
    edges=[]
    for anchor in range(16):
        pair=unused[2*anchor:2*anchor+2]
        if reverse:pair=pair[::-1]
        if order=='anchor-pairs':
            edges.extend([(anchor,16+anchor,weights[pair[0]]),
                          (anchor,16+(anchor+1)%16,weights[pair[1]])])
        else:
            edges.extend([(anchor,16+anchor,weights[pair[0]]),
                          ((anchor-1)%16,16+anchor,weights[pair[1]])])
    totals=[sum(w for _,v,w in edges if v==16+i) for i in range(16)]
    if totals==anchor_sums[:16]:boundary=edges;anchor_order={'order':order,'reverse':reverse};break
if boundary is None:
    # The grounded inverse fixes each center's sum of two anchor weights, not
    # their orientation. Choose an explicit valid orientation for a NEW model.
    candidates=[]
    for center in range(16):
        pairs=[(i,j) for offset,i in enumerate(unused) for j in unused[offset+1:]
               if weights[i]+weights[j]==anchor_sums[center]]
        if len(pairs)!=1:raise ValueError('Anchor pair is not uniquely determined by exact weights')
        candidates.append(pairs[0])
    if sorted(j for pair in candidates for j in pair)!=sorted(unused):
        raise ValueError('Anchor pairs do not partition all remaining weights')
    owner={j:center for center,pair in enumerate(candidates) for j in pair}
    boundary=[];anchors=set()
    for offset in range(0,32,2):
        i,j=unused[offset:offset+2];a,b=owner[i],owner[j]
        anchor=a if b==(a+1)%16 else b if a==(b+1)%16 else None
        if anchor is None or anchor in anchors:
            boundary=None;break
        anchors.add(anchor)
        boundary.extend([(anchor,16+a,weights[i]),(anchor,16+b,weights[j])])
    if boundary is not None and len(anchors)==16:
        anchor_order={'order':'independent-exact-center-sums-and-adjacent-weight-pairs',
                      'pairs_by_center':candidates,'all16_adjacent_anchor_pairs_checked':True}
    else:
        boundary=[]
        for center,(i,j) in enumerate(candidates):
            boundary.extend([(center,16+center,weights[i]),((center-1)%16,16+center,weights[j])])
        anchor_order={'order':'independent-exact-center-sums','pairs':candidates,
                      'orientation':'lower-original-weight-index to next anchor; other to previous'}

# Recover exact edge positions in the original numerator list. Repeated weights
# are matched deterministically; every later kernel must verify the same graph.
edge_pool={}
for u,v,w in witness_edges+boundary:edge_pool.setdefault(w,[]).append([u,v])
edges=[]
for w in weights:
    if not edge_pool.get(w):raise ValueError('Missing edge in complete source weight order')
    edges.append(edge_pool[w].pop(0))
if len({tuple(sorted(e)) for e in edges})!=134:raise ValueError('Repeated physical rod')

def adjacency(faces):
    graph=[set() for _ in range(26)]
    for f in faces:
        for a in f:graph[a].update(x for x in f if x!=a)
    return graph
target=json.loads((HERE.parent/'round-20261107b/topology.json').read_text())['faces']
left,right=adjacency(faces),adjacency(target)
mapping={i:i for i in range(16)}
def complete():
    if len(mapping)==26:
        return {tuple(sorted(mapping[x] for x in f)) for f in faces}=={tuple(sorted(f)) for f in target}
    candidates=[]
    for i in range(16,26):
        if i in mapping:continue
        allowed=[j for j in range(16,26) if j not in mapping.values() and len(left[i])==len(right[j])
                 and all((v in left[i])==(mapped in right[j]) for v,mapped in mapping.items())]
        if not allowed:return False
        candidates.append((len(allowed),i,allowed))
    _,i,allowed=min(candidates)
    for j in allowed:
        mapping[i]=j
        if complete():return True
        del mapping[i]
    return False
if not complete():raise ValueError('Recovered source graph is not the independently checked candidate topology')
result={'vertices':76,'anchors':16,'free':60,'edges':edges,'faces_by_witness':faces,
    'explicit_anchor_weight_assignment':anchor_order,
    'old_anchor_weight_orientation_identity_not_assumed':True,
    'physical_to_independent_cover_labels':mapping,
    'source_support_sha256':hashlib.sha256((HERE/'supports/support-00.json').read_bytes()).hexdigest(),
    'all_60_exact_grounded_inverse_rows_checked':True,
    'candidate_face_isomorphism_with_boundary_labels_fixed_checked':True,
    'old_SYSTEM_bytes_recovered':False,'old_full_source_geometry_acceptance_performed':False,
    'new_geometric_payments':0,'global_optimality_proved':False}
path=HERE/'RECOVERED-PHYSICAL-GRAPH.json';payload=(json.dumps(result,indent=2)+'\n').encode()
if path.exists() and path.read_bytes()!=payload:
    previous=path.read_bytes();backup=HERE/('PHYSICAL-GRAPH-prior-'+hashlib.sha256(previous).hexdigest()[:12]+'.json')
    if not backup.exists():backup.write_bytes(previous)
path.write_bytes(payload)
print('PASS independent 134-rod model, exact kernel identities and candidate graph isomorphism')
print('interior label map',mapping)
