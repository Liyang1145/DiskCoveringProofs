# topology-audit-cc2 — independent audit plan (k10 cover -> dual disk -> 1000 classes)

Route: commandcode2 / deepseek/deepseek-v4.1-flash. Write scope: this directory only.
Read-only inputs: lead/K10-CATALOGUE-AUDIT.md, lead/BOUNDARY-OWNERSHIP-PROOF.md,
members/topology/COVER-TO-DUAL.md, members/structure/NO-CHORD-n14.md,
members/topology/gen_k10_catalogue.py, lead/k10-catalogue-corrected.json,
research-2026/n12-global/lead/INNER-ROOT-REDUCTION.md (read-only, counted, not trusted).

Target proposition under audit (P): for 0<r<=U=.33173203427623414 and any 14-disk cover of D
with exactly k=10 boundary-active disks, the (inner-root normalized) nearest-site dual is a
triangulated disk with outer 10-cycle, 3 or 4 distinct hubs, and no ring-ring chord; all such
disks are exactly the 1000 dihedral/hub classes of lead/k10-catalogue-corrected.json.

Interfaces attacked (one full audit):
 I1 same-arc inner-root -> does coverage of D survive, hence is the normalized configuration
    a cover (the ownership proof and the enumeration both consume "cover")?
 I2 bisector/private-arc -> connected ownership J_i, exactly 10 arcs / 10 switches:
    strictness of d<s, degenerate (zero-length) arcs, three-owner switches.
 I3 curved-dual collar -> is the hub part strictly inside gamma? can a hub-hub facet midpoint
    (or its ray) land on gamma? test a concrete degenerate configuration.
 I4 Euler-walk enumeration completeness -> independent re-enumeration + reverse check.
 I5 canonicalization -> independent dihedral action, count 1000, previously-claimed 1535.
Not audited: 85-graph k11 catalogue (its hypotheses are not established; cannot be global).

Status of findings: see FINDINGS.md (this directory). No claim is certified here; each item
gets an evidence path + repro command.
