"""Refine general filling by necessary subgraphs of simple internal vertex links."""
from collections import defaultdict
from general_collar_filling import start_states, children as unfiltered_children
from complete_simple_collar import bits

assert __debug__


def internal_links_possible(faces, vertices):
    for vertex in vertices:
        link = defaultdict(set)
        for mask in faces:
            if mask >> vertex & 1:
                pair = [v for v in bits(mask) if v != vertex]
                assert len(pair) == 2
                u, v = pair
                link[u].add(v);link[v].add(u)
        if any(len(adj) > 2 for adj in link.values()):
            return False
        remaining = set(link)
        while remaining:
            root = min(remaining)
            component, queue = {root}, [root]
            for u in queue:
                for v in link[u]:
                    if v not in component:
                        component.add(v);queue.append(v)
            remaining -= component
            if all(len(link[v]) == 2 for v in component) and component != set(link):
                return False
    return True


def children(state, N, B):
    following = unfiltered_children(state, N, B)
    if following is None:
        return None
    result = []
    old = set(state["faces"])
    for child in following:
        added = set(child["faces"])-old
        assert len(added) == 1
        vertex_set = bits(next(iter(added)))
        assert all(v >= B for v in vertex_set)
        if internal_links_possible(child["faces"], vertex_set):
            result.append(child)
    return result
