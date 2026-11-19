from itertools import combinations


def graph(b, labels, counts, ears):
    """Consecutive boundary points, exterior centers, interior centers, witnesses."""
    decorated = b == 10 and len(labels) == 1
    k = 2 if decorated else max(labels)+1
    exterior = range(b, 2*b)
    inner = range(2*b, 2*b+k)
    skeleton = [i for i in range(b) if i not in ears]
    links = [(i, exterior[i]) for i in range(b)]
    links += [((i+1) % b, exterior[i]) for i in range(b)]
    faces = []
    for i in ears:
        C,D,E = exterior[(i-1) % b],exterior[i],exterior[(i+1) % b]
        if decorated and i == 1:
            faces += [(C,D,inner[1]),(D,E,inner[1]),(E,C,inner[1])]
        else:
            faces.append((C,D,E))
    p = 0
    for j, (label, length) in enumerate(zip(labels, counts)):
        for _ in range(length):
            q = (p+1) % len(skeleton)
            faces.append((exterior[skeleton[p]], exterior[skeleton[q]], inner[label]))
            p = q
        if len(labels) > 1:
            faces.append((exterior[skeleton[p]], inner[label], inner[labels[(j+1) % len(labels)]]))
    for w, vertices in enumerate(faces, start=2*b+k):
        links += [(v,w) for v in vertices]
    return 2*b+k+len(faces), links


MAIN = 9,(0,1,2),(3,3,3),()


def cases(b):
    if b == 9:
        for m1 in range(b+1):
            for m2 in range(m1,b-m1+1):
                m3 = b-m1-m2
                if m3 >= m2:
                    yield b,(0,1,2),(m1,m2,m3),()
        for m1 in range(1,b):
            for m2 in range(m1,b-m1+1):
                for n1 in range((b-m1-m2)//2+1):
                    n2 = b-m1-m2-n1
                    yield b,(1,0,2,0),(m1,n1,m2,n2),()
    elif b == 10:
        for n_ears in range(b//2+1):
            for ears in combinations(range(1,b), n_ears):
                if any(j-i == 1 for i,j in zip(ears,ears[1:])):
                    continue
                m = b-n_ears
                for m1 in range(1,m//2+1):
                    yield b,(0,1),(m1,m-m1),ears
        for n_ears in range(1,b//2+1):
            for other_ears in combinations(range(3,b),n_ears-1):
                if any(j-i == 1 for i,j in zip(other_ears,other_ears[1:])):
                    continue
                yield b,(0,),(b-n_ears,),(1,)+other_ears


def boundary_pairs(b):
    for i,j in combinations(range(b),2):
        chain = tuple(range(i,j)) if 2*(j-i) <= b else (*range(i),*range(j,b))
        yield i,j,chain
