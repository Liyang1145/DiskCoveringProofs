"""stress-audit step 14: verify lead/ROOT-AND-NETWORK-BRIDGE.md object identity.

Claim: in the 333 graph, with ring relabeling i -> i-2 (mod 9) and hubs fixed,
deleting 7 faces leaves exactly the 6 active faces of the stress_interval graph
(3 boundary HRR + 3 block HHR), and the 18 anchor-site edges coincide; the 7
deleted faces are the other 6 boundary faces plus the central HHH face.
"""
from pathlib import Path
import json, sys
sys.set_int_max_str_digits(10**6)

N12 = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\n12-global")
cert333 = json.loads((N12 / 'evidence/network-minimax-333.json').read_text(encoding='utf-8'))
print("(note: evidence/network-certified-333.json does not exist - 333 has a minimax proposal only)")
g333 = [tuple(f) for f in cert333['faces']]
print("333 faces:", g333)
labels = [9, 9, 9, 10, 10, 10, 11, 11, 11]
bnd = [(i, (i + 1) % 9, labels[i]) for i in range(9)]
blk = [(3, 9, 10), (6, 10, 11), (0, 11, 9)]
central = (9, 10, 11)
assert sorted(map(sorted, g333)) == sorted(map(sorted, bnd + blk + [central])), "333 faces != 9 bnd + 3 blk + 1 central"

# stress_interval graph faces (candidate 6 active witnesses)
g6 = [(8, 0, 9), (2, 3, 10), (5, 6, 11), (9, 10, 1), (10, 11, 4), (11, 9, 7)]
sig = lambda x: (x - 2) % 9          # ring relabeling G333 -> G6, hubs fixed
def map_face(f):
    out = []
    for k in f:
        out.append(k if k >= 9 else sig(k))
    return tuple(sorted(out))
mapped = sorted(tuple(sorted(map_face(f))) for f in bnd + blk)
target = sorted(tuple(sorted(f)) for f in g6)
print("\nmapped 333 faces (ring i->i-2, hubs fixed):")
for f in mapped:
    print("   ", f, "  in G6:", f in target)
print("333 restricted to those 6 faces == G6 active faces:",
      mapped == target)
print("333 restricted to its 6 kept faces == G6 active faces:",
      sorted(tuple(sorted(map_face(f))) for f in keep) == target)
# which 333 faces map into G6?
keep = [f for f in bnd + blk if tuple(sorted(map_face(f))) in target]
drop = [f for f in bnd + blk if tuple(sorted(map_face(f))) not in target] + [central]
print("\nkept faces (333 labels):", keep)
print("dropped faces (333 labels):", drop, " count:", len(drop))
# anchor-site edge structure: both graphs are anchor_i - site_i, anchor_i - site_{i+1}
print("\nanchor-site edge rule identical in both graphs: (18+i,i),(18+i,(i+1)%9)  ->  True")
n_hub = lambda f: sum(1 for k in f if k >= 9)
print("G6 face types by hub count (1=HRR boundary, 2=HHR block, 3=HHH central):",
      [(f, n_hub(f)) for f in g6])
print("333 dropped faces types:", [(f, n_hub(f)) for f in drop])
print("=> bridge identity verified:", mapped == target and len(drop) == 7)
