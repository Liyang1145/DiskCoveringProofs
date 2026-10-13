# Orbit check for the q0(6,7) label placements: the surviving class has hub degrees (6,7) <=> the two
# hubs own contiguous boundary chains of 5 and 4 edges; the two faces carrying the hub-hub edge have
# third vertices u,v (distinct ring labels).  Claim: all placements are ONE orbit under
# D_9 (rotations+reflections) x hub exchange.
import itertools
n = 9
def rot(a, k): return {(i, (i+k) % n) for (i, j) in a}
def refl(a, k=0):  # reflection i -> (k - i) mod n, applied to both ends
    return {((k - i) % n, (k - j) % n) for (i, j) in a}
# a placement = (frozenset of the 5 edges owned by hub A, frozenset of the 4 edges owned by hub B)
# chains: A owns {u,...,v} of length m along the cycle (m=5), B owns the complement (4 edges).
placements = set()
for u in range(n):
    for m in (5, 4):                      # A's chain length; v = u + m
        v = (u + m) % n
        A = frozenset(((u + t) % n, (u + t + 1) % n) for t in range(m))
        all_edges = frozenset((i, (i + 1) % n) for i in range(n))
        B = all_edges - A
        placements.add((A, B, u, v))
print('placements (u, m):', len(placements))
# group action: D_9 on edges, plus hub exchange
def act(p, g):
    A, B, u, v = p
    A2, B2 = g(A), g(B)
    return (frozenset(A2), frozenset(B2))
group = []
for k in range(n):
    group.append(lambda a, k=k: rot(a, k))
    group.append(lambda a, k=k: refl(a, k))
seen = set()
orbits = 0
for p in placements:
    key = (p[0], p[1])
    if key in seen: continue
    orbits += 1
    stack = [p]
    while stack:
        q = stack.pop()
        for g in group:
            A2, B2 = g(q[0]), g(q[1])
            for (A3, B3) in ((frozenset(A2), frozenset(B2)), (frozenset(B2), frozenset(A2))):
                if (A3, B3) not in seen:
                    seen.add((A3, B3))
                    stack.append((A3, B3, None, None))
print('orbits under D_9 x hub-exchange:', orbits, ' distinct configurations:', len(seen))
# also: the two hub-hub faces have third vertices u = chain start of one and v = its end; check the
# canonical representative u=0, m=4 -> v=4 (matching the saved candidate: two-hub faces (0,9,10),(4,9,10))
p = [p for p in placements if p[2] == 0 and p[3] == 4]
print('canonical rep (u=0,v=4):', len(p), 'edge sets; A-chain =', sorted(p[0][0]), 'B-chain =', sorted(p[0][1]))
print('saved candidate two-hub faces were (0,9,10) and (4,9,10) -> u=0, v=4, consistent:', any(pp[2]==0 and pp[3]==4 for pp in placements))
