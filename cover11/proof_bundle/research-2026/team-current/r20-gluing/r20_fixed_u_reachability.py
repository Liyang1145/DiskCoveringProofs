"""R20-FIXED-U-REACHABILITY (r20-gluing, cline2 / DS v4.1f): data export + independent exact
reachability check for r20-geometry's FIXED-U-PRIMAL-UNIQUENESS-LEMMA.md (Lemma 1 / Corollary 2).

Input (read-only): r20-alternative/socp_anchor_export.json  — the SOCP oracle solution of
lead/FIXED-SWITCH-SOC-REDUCTION.md §2: 51 constraints = 18 endpoint (|c_i - U_k| <= t) +
33 face-incidence (|c_s - z_f| <= t), with dual multipliers alpha = 2r*lambda.

This script
  * re-exports the data in the schema of r20-geometry/fixed_u_primal_uniqueness.py
    ({"anchors":[...], "nodes":[...], "edges":[[v,w,alpha],...]}) -> r20_fixed_u_dual_export.json;
    hubs are named c9 (= a) and c10 (= b) so that the checker's site test (name startswith "c")
    covers all ELEVEN sites; the mapping is recorded in the json;
  * runs an INDEPENDENT union-find/BFS replication of that checker's semantics
    (G+ = {alpha > 0}; anchored = components meeting an anchor; unpinned = nodes - anchored;
    sites = nodes starting with "c"), with a calibration self-test on synthetic path/cycle data;
  * does NOT write anything outside r20-gluing (r20-geometry's own script writes its .out.txt into
    its own directory, so it was not run here — the exported json is handed over for that run).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_fixed_u_reachability.py
"""
import json
import sys
from collections import defaultdict, deque
from pathlib import Path

HERE = Path(__file__).parent
ALT = HERE.parent / 'r20-alternative' / 'socp_anchor_export.json'
OUT_TXT = []


def say(*a):
    s = ' '.join(str(x) for x in a)
    OUT_TXT.append(s)
    print(s)
    sys.stdout.flush()


def reach(nodes, anchors, edges):
    """edges: list of (v, w, alpha) -> (components, anchored, unpinned, n_pos_edges)."""
    adj = defaultdict(set)
    npos = 0
    for (v, w, al) in edges:
        if al > 0:
            adj[v].add(w); adj[w].add(v); npos += 1
    aset = set(anchors)
    seen, comps = set(), []
    for s in nodes:
        if s in seen:
            continue
        comp, q = set(), deque([s]); seen.add(s)
        while q:
            u = q.popleft(); comp.add(u)
            for w in adj[u]:
                if w not in seen:
                    seen.add(w); q.append(w)
        comps.append(comp)
    anchored = set()
    for c in comps:
        if c & aset:
            anchored |= c
    unpinned = set(nodes) - anchored
    return comps, anchored, unpinned, npos


def main():
    # ---------------- calibration self-test (same semantics as the r20-geometry routine)
    say('=== self-test (calibration of my independent implementation) ===')
    n1 = ['U0', 'U1', 'c0', 'c1', 's0']
    e1 = [('U0', 'c0', 1.0), ('c0', 'c1', 1.0), ('c1', 'U1', 1.0), ('c1', 's0', 0.0)]
    c, a, u, np1 = reach(n1, ['U0', 'U1'], e1)
    say('  A (path, sites anchored, s0 slack): unpinned = %s -> PASS = %s'
        % (sorted(u), sorted(u) == ['s0']))
    n2 = ['U0', 'c0', 'c1', 'c2']
    e2 = [('c0', 'c1', 1.0), ('c1', 'c2', 1.0), ('c2', 'c0', 1.0), ('U0', 'c1', 0.0)]
    c2, a2, u2, np2 = reach(n2, ['U0'], e2)
    say('  B (anchor-free cycle): unpinned sites = %s -> correctly FLAGS = %s'
        % (sorted(x for x in u2 if x.startswith('c')),
           sorted(x for x in u2 if x.startswith('c')) == ['c0', 'c1', 'c2']))

    # ---------------- load the oracle data
    o = json.loads(ALT.read_text(encoding='utf-8'))
    inc = o['incidence_map']
    al = [float(x) for x in o['alpha_all_51_norm_form_2r_lambda']]
    lam = [float(x) for x in o['lambda_all_51_squared_form']]
    say()
    say('=== oracle data: %s ===' % ALT.name)
    say('  scope=%s' % o['scope'][:90])
    say('  51 constraints = 18 endpoint + 33 face-incidence ; sum(alpha) = %.16f'
        % sum(al))
    say('  alpha > 0 : %d ; alpha == 0 (exact) : %d ; alpha < 0 : %d'
        % (sum(1 for x in al if x > 0), sum(1 for x in al if x == 0), sum(1 for x in al if x < 0)))
    say('  (H1) "all edges strictly positive" as literally stated: %s'
        % ('HOLDS' if all(x > 0 for x in al) else 'FAILS (%d zero-alpha edges)' % sum(1 for x in al if x == 0)))
    say('  (H2) budget tightness sum alpha = 1: %s (deviation %.3e)'
        % (abs(sum(al) - 1) < 1e-12, sum(al) - 1))
    say('  V = %.16f ; R_star = %.16f ; V - R_star = %.3e'
        % (o['V'], o['R_star'], o['V_minus_R_star']))

    # ---------------- build the graph in the checker's schema
    anchors = ['U%d' % k for k in range(9)]
    nodes = ['c%d' % i for i in range(11)] + ['z%d' % f for f in range(11)]
    edges = []
    kinds = []
    for e, x in zip(inc, al):
        if e[0] == 'endpoint':
            i, k = int(e[1]), int(e[2])
            edges.append(['c%d' % i, 'U%d' % k, x]); kinds.append('endpoint')
        elif e[0] == 'face':
            f, s = int(e[1]), int(e[2])
            edges.append(['c%d' % s, 'z%d' % f, x]); kinds.append('face')
        else:
            raise ValueError('unknown incidence kind %r' % (e,))
    export = dict(anchors=anchors, nodes=nodes, edges=edges,
                  naming=dict(hubs='c9 = a, c10 = b (order taken from socp_anchor_export.json '
                                   'C_sites[9], C_sites[10])',
                              aux='z0..z10 = the 11 free face vertices of the SOC reduction',
                              sites='all names starting with "c" (11 sites)',
                              source='research-2026/team-current/r20-alternative/socp_anchor_export.json',
                              alpha='alpha = 2r*lambda, the norm-form SOC dual multipliers'),
                  notes=('naming convention chosen so the checker site-test (startswith "c") '
                         'covers all eleven sites including the two hubs; edge order/rota is '
                         'irrelevant for the undirected reachability test'))
    (HERE / 'r20_fixed_u_dual_export.json').write_text(json.dumps(export, indent=1))

    # ---------------- independent reachability run
    comps, anchored, unpinned, npos = reach(nodes, anchors,
                                            [(v, w, x) for v, w, x in edges])
    sites = [n for n in nodes if n.startswith('c')]
    unpinned_sites = sorted(s for s in sites if s in unpinned)
    say()
    say('=== independent reachability on the exported graph ===')
    say('  nodes %d (11 sites c0..c10 + 11 aux z0..z10) ; anchors %d ; positive edges %d/%d'
        % (len(nodes), len(anchors), npos, len(edges)))
    say('  components %d ; components containing an anchor %d'
        % (len(comps), sum(1 for c_ in comps if c_ & set(anchors))))
    for idx, c_ in enumerate(comps):
        cs = sorted(c_)
        tag = 'ANCHORED' if (c_ & set(anchors)) else 'UNANCHORED'
        say('    comp %d [%s]: %s' % (idx, tag, cs))
    say('  UNPINNED SITES: %s' % (unpinned_sites or 'none'))
    say('  unpinned aux/nodes (non-site): %s'
        % sorted(x for x in unpinned if not x.startswith('c')))
    say('  Lemma 1 / Corollary 2 combinatorial precondition (all sites anchored): %s'
        % (not unpinned_sites))
    # which zero-alpha edges are incident to sites with no positive edge
    zero_site_edges = [(v, w) for (v, w, x) in edges if x == 0 and (v.startswith('c') or w.startswith('c'))]
    say('  zero-alpha edges incident to a site: %d %s' % (len(zero_site_edges), zero_site_edges[:12]))

    # ---------------- robustness: how far can the positive-edge set be pruned?
    say()
    say('=== robustness sweep: keep only alpha >= tau, re-run the anchoring test ===')
    pos = sorted(x for x in al if x > 0)
    say('  positive alpha magnitudes: min %.3e (2^-54 = %.3e), %d below 1e-12, %d >= 1e-3'
        % (pos[0], 2.0 ** -54, sum(1 for x in pos if x < 1e-12), sum(1 for x in pos if x >= 1e-3)))
    sweep = []
    for tau in [0.0, 1e-16, 1e-14, 1e-12, 1e-10, 1e-8, 1e-6, 1e-4, 1e-3, 1e-2]:
        ee = [(v, w, x) for (v, w, x) in edges if x >= tau]
        cc, aa_, uu, np_ = reach(nodes, anchors, ee)
        ups = sorted(s for s in sites if s in uu)
        sweep.append(dict(tau=tau, nedges=len(ee), npositive=sum(1 for (_, _, x) in ee if x > 0),
                          unpinned_sites=ups, ok=not ups))
        say('  tau = %-8g : edges kept %2d ; unpinned sites %s %s'
            % (tau, len(ee), ups or 'none', '' if not ups else '<-- anchoring BREAKS'))
    (HERE / 'r20_fixed_u_reachability.out.txt').write_text('\n'.join(OUT_TXT) + '\n')
    (HERE / 'r20_fixed_u_sweep.json').write_text(json.dumps(sweep, indent=1))
    print('wrote r20_fixed_u_dual_export.json, r20_fixed_u_reachability.out.txt, r20_fixed_u_sweep.json')


if __name__ == '__main__':
    main()
