"""KKT exclusion for the scalar angular budget on a specified closed box."""
from intervals import I, Q, AD
from verify_local import isolate_root, parameters, angle_derivatives, gradient, det3
from fractions import Fraction

def corners(x):
    return I.raw(x.lo,x.lo), I.raw(x.hi,x.hi)

def cutoff(box,domain,grad):
    # A maximum can only have a positive partial derivative at its upper boundary.
    # Likewise a negative partial derivative requires its lower boundary.
    return any((g.lo>0 and x.hi<d.hi) or (g.hi<0 and x.lo>d.lo)
               for g,x,d in zip(grad,box,domain))

def negative_hessian(r,mu,lam,box):
    z=[AD.variable(v,k) for k,v in enumerate(box)]
    grad=gradient(r,mu,lam,*z)
    h=[[-v for v in s.d] for s in grad]
    return (h[0][0].lo>0 and (h[0][0]*h[1][1]-h[0][1]*h[1][0]).lo>0
            and det3(h).lo>0)

def check():
    r,a,t=isolate_root()
    u,b,c,mu,lam=parameters(r,a,t)
    root=[a,t,c]
    domain=[I.raw(I(lo).lo,I(hi).hi) for lo,hi in
            [('.23','.33'),('.375','.45'),('.83','.91')]]
    # Independently certified consensus signs in the relevant range.
    assert (1-(domain[1]+r)*(domain[1]+r)-r*r).lo>0
    assert (domain[2]*domain[2]-(domain[0]+r)*(domain[0]+r)-r*r).lo>0
    queue=[domain]
    counts=[0,0,0]
    stackmax=0
    while queue:
        box=queue.pop()
        try:
            if cutoff(box,domain,gradient(r,mu,lam,*box)):
                counts[0]+=1
                continue
            expanded=[I.raw(min(v.lo,q.lo),max(v.hi,q.hi)) for v,q in zip(box,root)]
            if max(x.hi-x.lo for x in expanded)<Q//600:
                if negative_hessian(r,mu,lam,expanded):
                    counts[1]+=1
                    continue
        except AssertionError:
            # A too-wide expression interval crossed zero or a square-root boundary.
            pass
        k=max(range(3),key=lambda j:box[j].hi-box[j].lo)
        middle=(box[k].hi+box[k].lo)//2
        assert box[k].lo<middle<box[k].hi
        left,right=box.copy(),box.copy()
        left[k]=I.raw(box[k].lo,middle)
        right[k]=I.raw(middle,box[k].hi)
        queue.extend([left,right]);counts[2]+=1
        stackmax=max(stackmax,len(queue))
    print('global angular budget bound on box [0.23,0.33] x [0.375,0.45] x [0.83,0.91]')
    print('boxes excluded by a derivative sign, by concavity to root, split:',
          *counts,'max stack',stackmax)
if __name__=='__main__':
    check()
