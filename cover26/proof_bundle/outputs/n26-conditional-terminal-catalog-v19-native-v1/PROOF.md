# Exact catalogue of selected current unresolved terminal paths

This catalogue covers exactly the terminal paths explicitly retained by the
bound current stage trace. It is not the complete four-family catalogue and
does not pay any geometric lower bound or remove any pending state.

Every path is resolved again by the independent peeling recurrence and must
be a full 26-vertex triangulated disk with the stated boundary. Its current
frontier entry must remain identical. Each face has three labels, each boundary
edge has one incident face, other edges have two, vertex links are connected
paths/cycles with the prescribed boundary endpoints, and Euler characteristic
is one. The rooted dual traversal must visit every face and label every vertex.

For every oriented boundary root, form the boundary degree profile, retain all
roots attaining the lexicographic minimum, and deterministically label interior
vertices at first discovery in the rooted dual BFS. Sort the relabelled face
masks; retain all roots attaining the minimum face code.
The degree filter is an invariant over the full boundary dihedral action,
not a heuristic discarded root. Identical codes provide explicit bijections
preserving the full triangular complex and cyclic boundary, and every such
stored bijection is checked face-by-face.

Fresh one-node terminal solve runs of the frozen native enumerator compute
its canonical codes. The Python implementation instead uses dictionary/set
incidence and a queue. All selected codes and stabilizer multiplicities must
agree exactly. No finite regression asserts global correctness for all future
graphs: these selected finite states are independently reconstructed.

Selected paths are grouped only when their full canonical codes coincide.
They remain pending even when duplicate; code equality is not a radius proof.
The known exact candidate terminal must be retained and its canonical class
identified. Missing paths, missing native runs, discarded frontier terminals,
nonbijective maps and incorrect face images are rejected.
