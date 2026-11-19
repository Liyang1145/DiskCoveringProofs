"""Enumerate short core chords and bound completions with three inner vertices."""
from collections import Counter
from itertools import combinations
from math import comb

K=10


def independent(indices):
    s=set(indices)
    return all((i+1)%K not in s for i in s)


def consecutive_on_cycle(a,b,removed):
    return (b-a)%K==1 or ((b-a)%K==2 and (a+1)%K in removed)


def verify():
    possible=Counter()
    for j in range(6):
        for ears in combinations(range(K),j):
            if not independent(ears):
                continue
            remaining=tuple(i for i in range(K) if i not in ears)
            if not all(consecutive_on_cycle(a,b,ears) for a,b in zip(remaining,remaining[1:]+remaining[:1])):
                raise ValueError("middle polygon edge skipped two core vertices")
            boundary={tuple(sorted((a,b))) for a,b in zip(remaining,remaining[1:]+remaining[:1])}
            ears_faces=[((i-1)%K,i,(i+1)%K) for i in ears]
            if any(tuple(sorted((face[0],face[2]))) not in boundary for face in ears_faces):
                raise ValueError("short chord does not bound its expected ear")
            possible[j]+=1
    expected={j:comb(K-j,j)*K//(K-j) for j in range(6)}
    if dict(possible)!=expected:
        raise ValueError("independent short-chord count")
    print(f"PASS B=14: {sum(possible.values())} choices of inner chords, counted before rotations, reflections or geometry of the three enclosed centers.")
    print(dict(possible))


if __name__=="__main__":
    verify()
