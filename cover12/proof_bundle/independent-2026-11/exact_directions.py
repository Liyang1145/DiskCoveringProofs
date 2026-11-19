"""Exact Cartesian enclosures for the polar angular cells."""
import argparse
from fractions import Fraction as Q
from balanced import Iv, S, cos_range
from exact_angles import TURN, SCALE, PI_LO, PI_HI, check_constants


def at_cos(t):
    t %= TURN
    if t > TURN//2:
        t=TURN-t
    negative=t>TURN//4
    if negative:
        t=TURN//2-t
    a=Iv(2*PI_LO*t/TURN,2*PI_HI*t/TURN)
    value=cos_range(a)
    return -value if negative else value


def between(lo,hi,shift):
    a,b=lo-shift,hi-shift
    ends=[at_cos(a),at_cos(b)]
    for t in range(-TURN,2*TURN,TURN//2):
        if a<=t<=b:
            ends.append(Iv(1 if t%TURN==0 else -1))
    inf=min(x.lo for x in ends)
    sup=max(x.hi for x in ends)
    return inf*SCALE//S, -((-sup*SCALE)//S)

def good_boxes():
    angles = [
        0, TURN*1086//10000, TURN*2247//10000, TURN//3,
        TURN*4420//10000, TURN*5580//10000, 2*TURN//3,
        TURN*7753//10000, TURN*8914//10000, TURN//6, TURN//2, 5*TURN//6,
    ]
    boxes=[]
    for i,a in enumerate(angles):
        if i==0:
            boxes.append((0,0,720000000,933000000))
        elif i in (3,6):
            b=TURN*4//100
            boxes.append((a-b,a+b,720000000,933000000))
        elif i<9:
            b=TURN*5//100
            boxes.append((a-b,a+b,780000000,933000000))
        else:
            b=TURN*25//1000
            boxes.append((a-b,a+b,230000000,330000000))
    return boxes

def verify_good(boxes):
    """The product of these twelve ranges satisfies the balanced lemma."""
    from exact_angles import R
    r=Q(R,SCALE)
    assert Q(".33") < Q(".361102963")
    c=cos_range(Iv(2*PI_LO/5,2*PI_HI/5))
    assert (1-c.sq()).sqrt().lo > Iv(".95").hi
    assert Q(".78")*Q(".95") > 2*r
    assert Q(".72")**2+Q(".23")**2 > 4*r*r

    def separation(i,j):
        a,b=boxes[i][:2]
        c,d=boxes[j][:2]
        return min(max(0,c+k-b,a-d-k) for k in (-TURN,0,TURN))

    def disjoint(outer,inner):
        return separation(outer,inner)>=TURN//(4 if outer%3==0 else 5)

    for i in range(3):
        j,k=9+i,9+(i+1)%3
        assert max(boxes[j][1],boxes[k][1])<TURN
        lo=boxes[k][0]-boxes[j][1]+(TURN if k<j else 0)
        hi=boxes[k][1]-boxes[j][0]+(TURN if k<j else 0)
        assert 60*lo>=17*TURN and 60*hi<=23*TURN
        left,right=3*i+1,3*i+2
        for other in range(9,12):
            if other!=j:
                assert disjoint(left,other) or disjoint(right,other)
        for other in range(9):
            if other!=(3*i+3)%9:
                assert disjoint(other,j) or disjoint(other,k)
    c0=cos_range(Iv(17*PI_LO/30,17*PI_HI/30))
    c1=cos_range(Iv(23*PI_LO/30,23*PI_HI/30))
    assert c0.hi < Iv("-.207").lo and c1.lo > Iv("-.744").hi
    a=Q(".23")
    for b in (a,Q(".33")):
        for c in (a,Q(".33")):
            assert a*a+Q(".207")*a*(b+c)-Q(".744")*b*c>0

def directions(n):
    assert TURN%n==0
    good=good_boxes()
    verify_good(good)
    for k,row in enumerate(good):
        yield -1,k,*row
    yield 0,0,SCALE,SCALE,0,0
    for j in range(n):
        a,b=TURN*j//n,TURN*(j+1)//n
        yield a,b,*between(a,b,0),*between(a,b,TURN//4)


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("n_angles",type=int)
    p.add_argument("output")
    args=p.parse_args()
    check_constants()
    with open(args.output,"w",encoding="ascii") as out:
        for row in directions(args.n_angles):
            print(*row,file=out)
