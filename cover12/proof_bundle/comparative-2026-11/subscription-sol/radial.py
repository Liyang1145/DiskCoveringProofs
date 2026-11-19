from bisect import bisect_left

from intervals import Interval, ONE, PI, Q, SCALE, ZERO, cos, sin
from network import R


TESTS = [(1000,6440),(305,443),(365,232),(325,1030),(400,1277),(420,578)]


def acos_upper_table():
    step = Q(1,2000)
    c,s = cos(step),sin(step)
    a,b = ONE,ZERO
    cosine_upper = [-SCALE]
    for _ in range(PI.lo//step.hi):
        a,b = c*a-s*b,s*a+c*b
        cosine_upper.append(-a.hi)
    assert all(a < b for a,b in zip(cosine_upper,cosine_upper[1:]))

    def acos_upper(lo):
        j = bisect_left(cosine_upper,-lo)
        return j*step.hi if j < len(cosine_upper) else PI.hi

    return acos_upper


def enclosure(t, p_low, p_high, acos_upper):
    a = t.square() - R.square()
    if a.hi < 0 and p_low == 0:
        return PI.hi
    l,h = Interval(p_low,p_low),Interval(p_high,p_high)
    if a.hi < 0 or l.square().lo >= a.hi:
        c = (l+a/l)/(2*t)
    elif h.square().hi <= a.lo:
        c = (h+a/h)/(2*t)
    else:
        assert a.lo > 0
        c = a.sqrt()/t
    return acos_upper(c.lo)


def replay_radial():
    arc_upper = acos_upper_table()
    step = Q(1,10000).lo
    tests = [(Q(t,1000),w) for t,w in TESTS]
    assert sum(w for t,w in tests)==10000

    def maximum(lo,hi):
        return max(sum(w*enclosure(t,p,min(p+step,hi),arc_upper) for t,w in tests)
                   for p in range(lo,hi,step))

    a = maximum((1-R).lo,ONE.hi)
    b = maximum(0,(3*R-1).hi)
    margin = PI.lo*10000-11*a-b
    assert margin > Q(1,50).hi*10000
    print(f'11 boundary cells: six-circle arcs, floor(10^6 * strict margin) = {margin*100//SCALE}')
