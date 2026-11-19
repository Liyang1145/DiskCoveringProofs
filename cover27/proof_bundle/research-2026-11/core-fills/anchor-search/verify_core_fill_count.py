"""Independently count the labelled core fills by removing boundary faces."""
from functools import cache

from verify_b14_core_marks import K


def edge(a,b):
    return (a,b) if a<b else (b,a)


def possible(a,b,forbidden):
    return (a>=K or b>=K or min((a-b)%K,(b-a)%K)<=2) and edge(a,b) not in forbidden


def subproblem(cycle,inside,forbidden):
    if len(cycle)==2:
        return int(not inside)
    if len(cycle)<3:
        raise ValueError("too few boundary vertices")
    first=cycle.index(min(cycle))
    cycle=cycle[first:]+cycle[:first]
    vertices=set(cycle).union(inside)
    kept=tuple(e for e in forbidden if all(i in vertices for i in e))
    return count(cycle,inside,kept)


@cache
def count(cycle,inside,forbidden):
    a,b,*_=cycle
    if not possible(a,b,forbidden):
        raise ValueError("forbidden boundary edge")
    answer=0
    for j,c in enumerate(cycle[2:],2):
        if not possible(a,c,forbidden) or not possible(b,c,forbidden):
            continue
        left,right=cycle[1:j+1],cycle[j:]+cycle[:1]
        for mask in range(1<<len(inside)):
            x=tuple(i for k,i in enumerate(inside) if mask>>k&1)
            y=tuple(i for k,i in enumerate(inside) if not (mask>>k&1))
            answer+=subproblem(left,x,forbidden)*subproblem(right,y,forbidden)
    for c in inside:
        f=tuple(sorted((*forbidden,edge(a,b))))
        answer+=subproblem((a,c,*cycle[1:]),tuple(i for i in inside if i!=c),f)
    return answer


def verify(expected):
    result=subproblem(tuple(range(K)),tuple(range(K,K+3)),())
    if result!=6*expected:
        raise ValueError(f"core-fill count mismatch: {result} labelled fills, catalogue has {expected} unlabelled interiors")
    print(f"PASS B=14: independent boundary-face recursion counts {result} fully labelled core triangulations.")
    return result


if __name__=="__main__":
    verify(49805)
