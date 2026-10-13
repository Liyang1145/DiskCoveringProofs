"""r20-geometry Round-17 (lead 525c806e): exact combinatorial reachability for the fixed-U uniqueness lemma.

Given the oracle's dual multipliers (list of (edge, alpha)), this script:
  1. builds the positive-edge graph G+ = {e : alpha_e > 0};
  2. BFS/union-find from the anchor set;
  3. reports every free NODE's component and whether it contains an anchor (sites must all be anchored);
  4. runs a calibrated self-test on synthetic path/cycle instances before application.

Run modes:
  py -3 -B -X utf8 fixed_u_primal_uniqueness.py                 # self-test only (no oracle data)
  py -3 -B -X utf8 fixed_u_primal_uniqueness.py dual.json       # apply to oracle data
where dual.json = {"anchors": ["U0",...], "nodes": ["c0",...,"z0",...],
                   "edges": [["c0","U0",alpha], ...]}  (alpha as string/number)
"""
import io, json, sys
from collections import deque, defaultdict

OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


def reachability(nodes, anchors, edges):
    """edges: list of (v, w, alpha). Returns (components, anchored_nodes, unpinned)."""
    adj = defaultdict(set)
    pos_graph = []
    for (v, w, al) in edges:
        if al > 0:
            adj[v].add(w)
            adj[w].add(v)
            pos_graph.append((v, w))
    anchor_set = set(anchors)
    seen, comp_of = set(), {}
    comps = []
    for s in nodes:
        if s in seen:
            continue
        comp, q = set(), deque([s])
        seen.add(s)
        while q:
            u = q.popleft()
            comp.add(u)
            for w in adj[u]:
                if w not in seen:
                    seen.add(w)
                    q.append(w)
        comps.append(comp)
        for u in comp:
            comp_of[u] = len(comps) - 1
    anchored = set()
    for i, comp in enumerate(comps):
        if comp & anchor_set:
            anchored |= comp
    unpinned = set(nodes) - anchored
    return comps, anchored, unpinned, pos_graph


def report(nodes, anchors, edges, sites, label):
    comps, anchored, unpinned, pos_graph = reachability(nodes, anchors, edges)
    say("== %s ==" % label)
    say("  nodes: %d ; anchors: %d ; positive edges: %d" % (len(nodes), len(anchors), len(pos_graph)))
    say("  components: %d ; components containing an anchor: %d"
        % (len(comps), sum(1 for c in comps if c & set(anchors))))
    unpinned_sites = [s for s in sites if s in unpinned]
    say("  unpinned nodes: %d %s" % (len(unpinned), sorted(unpinned) if len(unpinned) <= 12 else ""))
    say("  UNPINNED SITES (must be empty for Lemma 1/Corollary 2): %s" % (sorted(unpinned_sites) or "none"))
    return not unpinned_sites


# ---------------- self-test ----------------
say("SELF-TEST (calibration of the routine)")
# path: U0 - c0 - c1 - U1 with positive alphas ; plus a free slack node s0 whose only edge has alpha = 0
nodes = ["U0", "U1", "c0", "c1", "s0"]
anchors = ["U0", "U1"]
edges = [("U0", "c0", 1.0), ("c0", "c1", 1.0), ("c1", "U1", 1.0), ("c1", "s0", 0.0)]
ok1 = report(nodes, anchors, edges, ["c0", "c1"], "self-test A (path, all sites anchored, s0 slack)")
# cycle without anchor contact: c0-c1 positive, no anchors in that component
nodes2 = ["U0", "c0", "c1", "c2"]
edges2 = [("c0", "c1", 1.0), ("c1", "c2", 1.0), ("c2", "c0", 1.0), ("U0", "c1", 0.0)]
ok2 = report(nodes2, ["U0"], edges2, ["c0", "c1", "c2"], "self-test B (anchor-free cycle -> sites MUST be flagged)")
say("")
say("self-test A passes (no unpinned sites): %s" % ok1)
say("self-test B correctly FLAGS unpinned sites: %s" % (not ok2))
say("")

# ---------------- optional application to oracle data ----------------
if len(sys.argv) > 1:
    data = json.load(io.open(sys.argv[1], encoding="utf-8"))
    nodes = list(data["nodes"])
    anchors = list(data["anchors"])
    edges = [(v, w, float(al)) for (v, w, al) in data["edges"]]
    sites = [n for n in nodes if str(n).startswith("c")]
    ok = report(nodes, anchors, edges, sites, "ORACLE DATA: %s" % sys.argv[1])
    say("RESULT: all sites lie in anchored components: %s" % ok)
    say("Note: alpha > 0 tests are performed on the supplied values; if the oracle reports equality at 0,")
    say("      strict positivity is NOT established and the lemma's hypothesis (H1) must be re-examined.")
else:
    say("no oracle data supplied: the exact reachability obligation remains PENDING (self-test only).")
io.open('research-2026/team-current/r20-geometry/fixed_u_primal_uniqueness.out.txt', 'w',
        encoding='utf-8').write("\n".join(OUT) + "\n")
print()
print("wrote fixed_u_primal_uniqueness.out.txt")
