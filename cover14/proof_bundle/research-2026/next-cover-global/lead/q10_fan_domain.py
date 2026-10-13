"""C1331safe cuts expressedin existing Q³: (5/24)(10L−2pi)<.1, avoiding extra basisconstant."""
from q10_polytope_partition_probe import root,tri,Q,iv,P,json

def fan_root():
 delta=tri(10,0,-1);rhs=tuple(Q(5,24)*x for x in delta);assert iv(rhs).hi*Q(1,10**0)<Q(1,10)*__import__('q11_chord_polytope').S
 poly=root();reports=[]
 for ids in [[8,9,0,1],[3,4,5,6]]:
  nn=[Q(i in ids)for i in range(10)];poly,rejected,rep=poly.split(nn,rhs,'C1331fan'+str(ids[0]));reports.append(rep)
 return poly,reports
if __name__=='__main__':
 poly,reports=fan_root();(P/'q10-fan-root.json').write_text(json.dumps({'status':'necessary_domain_C1331_childvertices_pendingindependentaudit','polytope':poly.to_dict(),'splits':reports},indent=2));print('FANROOT',len(poly.vertices))
