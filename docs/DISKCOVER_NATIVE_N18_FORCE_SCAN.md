<!-- SPDX-License-Identifier: MIT -->
# n=18 native noncandidate force scan

The three native census families have 397, 6,971 and 7,191 canonical
orbits. Exactly one orbit, in the twelve-owner family, is excluded by
the [candidate-wide hybrid replay](DISKCOVER_NATIVE_N18_CANDIDATE_REPLAY.md).
Every other orbit must be excluded by independent force-tree replay
or explicitly left unresolved.

The scanner binds fresh DFS/audit census rows to the stored canonical
hashes. It generates numerical LP proposals, but a row is accepted only
after exact rational verification of all tree partitions, support
halfplanes, force balances and strict separation inequalities. Force
uses the certified algebraic radius's strict rational upper endpoint;
force separation at that endpoint excludes every smaller realization.
The orbit graph is reconstructed from its census face masks. Root angles
are tightened by independently certified short-arc constraints. A failed
LP, exhausted depth, invalid receipt or missing row cannot prove anything.
A separate final pass reconstructs each tree from its atomic on-disk
chunk. Chunk progress is recoverable after interruption; keep partition
size unchanged when resuming to preserve the filename-to-index mapping.
The scan expects a single writer for any given chunk.

To generate or resume the eleven-owner family on one worker:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 \
    python -B verification/n18/force_census.py path/to/census path/to/chunks \
      --owners 11 --workers 1 --chunk 12 --depth 5 --directions 48

To regenerate depth-limited rows only, specify --retry-unresolved alongside
a larger --depth and/or --directions. To perform standard-library-only
verification, select --replay-only with the same --owners and --chunk.
An owner subset may be complete while the unrestricted global scan is
not; only a full three-family replay can set all_topologies_closed.

For twelve and thirteen owners, provide the exact positive-matrix root
data and pinned candidate tree linked in the candidate replay, so the
single skipped orbit is independently and freshly verified:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 \
    python -B verification/n18/force_census.py path/to/census path/to/chunks \
      --owners 12 13 --workers 1 --chunk 12 --depth 5 --directions 48 \
      --candidate-root path/to/root18.json \
      --candidate-tree path/to/candidate18_tree.json.gz

No generated force proof is needed for the candidate orbit. All other
orbits require force leaves with no open nodes. Loading the census or
creating a partial chunk is not an exclusion.

## Completed eleven-owner family

All **397** eleven-owner orbits were excluded by a single exact force
leaf each, with no angle splits. Fresh one-worker generation completed
all 34 durable chunks, then a standard-library pass independently
replayed every row. The deterministic archive
verification/n18/force_b11.json.gz ships those exact force vectors;
SHA-256 is 943310dc04a1c23d6e46df484aa30724088bd4445c03c8c02862000a35bfef54.

    python -B verification/n18/replay_b11_archive.py path/to/census

This rechecks every archived row, not a stored acceptance status; see
[the receipt](../verification/n18/force_b11_receipt.json). The result
eliminates all eleven-owner candidate-scale realizations. The 6,970
noncandidate twelve-owner orbits and all 7,191 thirteen-owner orbits
still need their own evidence.
