# MOVED — see `LOCALITY-LEMMA-RING.md`

The content of this file (three ring disks with a common point have consecutive indices) is now
**unified and superseded** by `LOCALITY-LEMMA-RING.md`, which states the locality lemma in its general
form:

* **L1** (two disks): index distance `>= 3` implies the closed disks are disjoint;
* **L2** (three disks): a common point forces consecutive indices `{i,i+1,i+2}`;
* **L3** (four disks): a common point is impossible;
* **L4** (graph form): the ring's intersection graph is a subgraph of `C_9²`;

all four from the same arc-capacity count (`J = ∂D ∩ B(p,2r)`, `|J| <= 2 asin(2r)`, staircase forces
the intermediate arcs into `J`, `>= 4` arcs in `J` contradict `π <= asin(2r) + 5 asin(r)`).

The two-neighbour reduction for O1 follows: `v_k` can lie only in `B_{k-1}` or `B_{k+2}`.
