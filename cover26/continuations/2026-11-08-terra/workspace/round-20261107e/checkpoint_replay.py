"""Replay the paused checkpoint. Successful replay does not close any OPEN box."""
from pathlib import Path
from fractions import Fraction as Q
from copy import deepcopy
from datetime import datetime, timezone
import hashlib, json
import reconstruct_domains as domains
import verify_kernels as old
from verify_fresh_kernels import verify
import exact_energy as energy

HERE=Path(__file__).resolve().parent
def read(p):return json.loads(p.read_text(encoding='utf-8'))
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as stream:
        for b in iter(lambda:stream.read(1048576),b''):h.update(b)
    return h.hexdigest()

def main():
    source=HERE/'native-recovered/n26-root25-current346-refit2-origin-append-composition-v1.json'
    old.demand(source.exists(),'Restore original arithmetic snapshot before this source-bound replay')
    old.demand(sha(source)=='c1675552b56d762de0bca83ca3adbb28e06c71e95c94b387d7f216eee41187c9','complete original source hash')
    old.run()
    model=read(HERE/'RECOVERED-PHYSICAL-GRAPH.json');edges=old.model_gate(model)
    data=read(HERE/'arithmetic-working-projection.json')
    cap=domains.caps();matrix,direct=domains.matrix_from_graph(model['faces_by_witness'],cap)
    boxes,_=domains.all_domains(data,matrix)
    pending=data['pending_closed_leaf_boxes']
    indices={row['index'] for row in pending}
    old.demand(len(indices)==len(pending)==344,'all 344 unique OPEN domains')
    old.demand(indices=={i for i,node in enumerate(data['nodes']) if node['kind']=='OPEN'},'complete OPEN inventory')
    for row in pending:
        old.demand(boxes[row['index']]==(list(map(Q,row['lower'])),list(map(Q,row['upper']))),'original closed OPEN box equality')
    saved=read(HERE/'DOMAIN-RECONSTRUCTION.json')
    old.demand([[str(x) for x in row] for row in matrix]==saved['matrix'],'fresh exact directed angular matrix')
    rejected=[]
    bad=deepcopy(data);root=bad['nodes'][0]
    old.demand(root['kind']=='SPLIT','split root')
    root['children']=root['children'][:1]
    try:domains.all_domains(bad,matrix)
    except ValueError:rejected.append('dropped-closed-child')
    else:raise ValueError('Dropped child accepted')
    row=pending[0];altered=list(map(Q,row['lower']));altered[0]+=Q(1,10**80)
    old.demand(boxes[row['index']]!=(altered,list(map(Q,row['upper']))),'perturbed source box must differ')
    rejected.append('perturbed-source-box')
    base={};fresh=[]
    for suffix in ('','-v01'):
        kernels=[]
        for owner in (16,25):
            p=HERE/'fresh-kernels'/('leaf-2136'+suffix+'-owner-'+str(owner)+'.json')
            result=verify(p,edges);kernels.append(result);base[suffix,owner]=result
        saved_k=read(HERE/'fresh-kernels'/('leaf-2136'+suffix+'-VERIFIED.json'))['kernels']
        old.demand(kernels==saved_k,'new kernels independently regenerated')
        fresh.extend(kernels)
    verified={('',k['origin_owner']):k for k in fresh[:2]}
    verified.update({('v01',k['origin_owner']):k for k in fresh[2:]})
    for label,w in [('mix50',Q(1,2)),('mix75',Q(3,4))]:
        for kernel in read(HERE/'fresh-kernels'/('leaf-2136-'+label+'-VERIFIED.json'))['kernels']:
            owner=kernel['origin_owner'];a,b=base['',owner],base['-v01',owner]
            ad={(i,j):int(lo) for i,j,lo,_ in a['pairs']};bd={(i,j):int(lo) for i,j,lo,_ in b['pairs']}
            pairs=[]
            for i in range(16):
                for j in range(i+1,16):
                    z=w*ad.get((i,j),0)+(1-w)*bd.get((i,j),0);v=z.numerator//z.denominator
                    if v:pairs.append([i,j,str(v),str(v)])
            z=w*int(a['constant_lower'])+(1-w)*int(b['constant_lower'])
            old.demand(pairs==kernel['pairs'] and str(z.numerator//z.denominator)==kernel['constant_lower'],'exact convex-mixture lower function')
            old.demand(kernel['reference_turns']==a['reference_turns'] and kernel['coefficient_denominator']==a['coefficient_denominator'],'mixture coordinates and scale')
            verified[label,owner]=kernel
    gaps=[]
    leaf=next(row for row in pending if row['index']==2136)
    for label in ('','v01','mix50','mix75'):
        stem='leaf-2136'+('-'+label if label else '')
        for proposal in read(HERE/'fresh-exclusions'/(stem+'-proposal.json')):
            kernel=verified[label,proposal['origin_owner']]
            info=energy.data(kernel,leaf,proposal['parts'])
            lower,pivots=energy.evaluate(info,proposal['curvature_correction'],proposal['quadratic_tangent'],proposal['difference_dual'],matrix,domains.SCALE)
            gap=lower-domains.RADIUS**2
            old.demand(str(lower)==proposal['exact_energy_lower'] and str(gap)==proposal['exact_strict_gap'],'fresh exact proposal replay')
            old.demand((gap>0)==proposal['passed_exact_margin_proposal'],'margin verdict follows arithmetic')
            old.demand(gap<=0,'Paused checkpoint must retain the failed exclusion status')
            gaps.append({'stage':label or 'base','origin_owner':proposal['origin_owner'],'strict_gap':str(gap),'approximate_gap':float(gap),'box_excluded':False})
            print('replayed failed whole-domain attempt',label or 'base',proposal['origin_owner'],float(gap),flush=True)
    report={'date':datetime.now(timezone.utc).isoformat(),'scope':'checkpoint replay: source hash, 29 exact kernels, all 2999 domains, 344 OPEN identities, four new kernels and eight failed margin attempts',
            'source_sha256':sha(source),'all_nodes_reconstructed':len(boxes),'open_domains_retained':344,'old_kernels_verified':29,
            'new_raw_kernels_verified':4,'negative_controls_rejected':rejected,'failed_margin_attempts':gaps,
            'new_closed_leaf_payments':0,'native_formal_roots':16,'native_conditional_frontier':4957,
            'historical_arithmetic_ledger_semantically_replayed':False,'original_system_identity_assumed':False,
            'global_optimality_proved':False,'continuous_goal_status':'paused','all_scoped_checks_passed':True}
    (HERE/'CHECKPOINT-REPLAY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('PASS checkpoint replay; zero new exclusions; 16 / 4957 / 344 retained')

if __name__=='__main__':main()
