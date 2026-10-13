# Strict mixed-N / mixed-scale replay: tooling, evidence, and acceptance

Scope: `members/finite-reduction/integer-domain/`.  Everything below is an **interface and
provenance verification of the frozen integer kernel's replay**; it is *not* an independent
proof of the covering-radius statement.  The independent partition verification is the
Lead's prefix tree; the mathematics lives in the Lead's reductions.

## 1. What is verified, and by what

| object | what is checked | where |
|---|---|---|
| per-leaf atom count `N` | dispatch 2048 → frozen `integer_kernel.IntAtoms`; 8192 → `integer_kernel_n.IntAtomsN` with the explicit canonical-8192 file; unknown N **refused** (never auto-generated) | `py/verify_manifest.py` |
| integer scale | per row `used_scale ∈ {26, 28}`; default 26 with escalation to 28 on kernel stop; escalation recorded | `py/verify_manifest.py`, `out/escalated-scale28-evidence.json` |
| margin | `status == "certified"` **and** `gap == demand − 10·max_capture > 0` recomputed row by row (gap 0 excludes nothing: T = 10M is an equality) | `py/check_results.py`, `py/acceptance_check.py` |
| content key | binds `N`, scale, vector-set hash, frozen kernel hash, N-kernel hash, full `sha256(H)`, full `sha256(W)`; **scale is part of the key** so a 26-certificate is not a 28-certificate | `py/verify_manifest.py`, `py/cache_tools.py` |
| cache promotion | snapshot-binding per row, full H/W hashes, strict positive gap, dedupe by key, atomic replace | `py/migrate_cache.py`, `py/cache_tools.py` |
| fresh ancestry | content-verified chains T1–T7 (source snapshot hash, leaf H/W/N, vectors, kernels, scale, gap arithmetic, certified status) | `py/cache_provenance.py` |
| legacy generations | explicit registry: exact file + allowed N + allowed scale + which fields may be absent, each with its evidence string | `LEGACY_ORIGINS` in `py/cache_provenance.py` |
| acceptance | every replay row's `ckey` must be in the verified provenance set; cache and provenance sha256 frozen | `py/acceptance_check.py` |

Negative controls (all pass): same-H/different-W, wrong snapshot field, unresolved verdict
with self-consistent key, negative gap, tampered key, `gap == 0`, missing gap, scale-26 vs
scale-28 non-interchange, N=2048 vs N=8192 non-interchange, `--build-cache` no longer able to
truncate the cache, `--expect-hash` mismatch now fatal.

## 2. Independence and disclaimers

* The integer kernel is **upper-audit's** frozen translation; replaying it is a **repeat
  execution**, not independent mathematics.  Independent parts here are the manifest
  tiling/prune/inference checks, the binding layer, and the negative controls.
* `check_results.py` / `acceptance_check.py` import `verify_manifest` helpers; they are
  **post-hoc interface checks**, not an independent implementation of the arithmetic.
* Do not describe these four scripts as an "independent full-core verification".

## 3. Current readings

| snapshot | sha256 | atomic | replay | certified | from cache | fresh | pending | verdict |
|---|---|---|---|---|---|---|---|---|
| stage11825 | `26fefd6a…d6d1` | 5603 | 5603 | 5603 | 5600 | 3 (scale 28) | 8 | partial-accepted |
| merged-partial-resume | `ba4397a3…8f90` | 6309 | 6309 | 6309 | 5603 | 706 | 10 | partial-accepted |
| final-wave-base | `71ead0af…4e665` | 6449 | 6449 | 6449 | 6309 | 140 | 7 | partial-accepted |
| **completed-domain-base** | **`7f44132b…c57a`** | **6723** | **6723** | **6723** | **6449** | **274** | **0** | **global** |

### Final domain (completed-domain-base.json)

* `atomic_replay`: 6723 atomic, 6723 certified, 0 not-certified, 0 unresolved, 0 budget,
  `idx_set_exact = true`, `pending_empty = true`, verdict `complete`,
  `global_certificate = true`;
* per-N histogram `{2048: 6031, 8192: 692}`, per-scale `{26: 6720, 28: 3}`;
* partition: `recursive_tiling_exact = true`, frontier 7041 = visited 7041, 0 unresolved,
  14081 nodes traversed (independent recursive tiling of the root, not containment+volume);
* all **318** infeasible leaves independently reproduced; prune3 187/187 consistent;
* acceptance gate: A1a–A1d, A2–A7 all true, 0 problems in every category.

Frozen hashes (`out/freeze-completed-domain.json`) — regenerated **after all writers stopped**,
with provenance's recorded cache hash byte-equal to the cache on disk:

```
snapshot      7f44132b8dd09c8377b7e300caebe6ca5485b8933bde86455f67062733c1c57a
cache         76a44a4e1988a6fa6ce237fb161a027cea75f78000ab478ee260732df96dd22e
provenance    0066dae3b7c2f656132bfa569fc820fa82317b09f5790d8355c28f44eab4904f
replay jsonl  d1f2e6e9be25d03001d6a7f665854b798cfb470bb1ba6ac986a1ae49b3ee0ee7
summary       244c3cce5f6e73b8a30a1d11b24dbca01453860c14008867c6d32b66605dccce
```

### Ordering rule (learned from a real failure)

The acceptance gate's A1b compares `provenance.cache_sha256` with the cache **as it is now**.
Because the witness binding writes into the cache, the order must be:

```
migrate_cache.py  ->  cache bytes final
bind_fresh_provenance.py  (writes witnesses, then AUTOMATICALLY re-runs cache_provenance)
acceptance_check.py --freeze
```

An earlier sequence (`provenance -> bind`) left provenance recording a stale cache hash and the
gate correctly refused the result — that is the control working, not a cosmetic mismatch.
A second real failure is also covered: running a *control* snapshot against the production
cache used to append synthetic entries into it.  `verify_manifest.py` now appends only for
snapshots that are registered production snapshots (or with an explicit `--append-cache`),
and `migrate_cache.py` admits rows only from the registered ledger set.

### Caliber of this "global"

Stated precisely: for this snapshot, every atomic leaf is certified by the frozen integer
kernel with a strictly positive recomputed margin, the leaves exactly tile the root box,
every infeasible leaf is reproduced independently, and the pending queue is empty.  The
gate is an **interface/provenance** gate.  It does **not** make the integer kernel an
independent proof of the covering-radius statement (it is upper-audit's frozen translation,
so replaying it is repeat execution), and it does not re-derive the Lead's reduction.  The
independent partition verification is the Lead's `check_partition_trie` evidence
(`evidence/completed-domain-prefix-partition.json`).

All three: exact partition, all infeasible prunes reproduced (274 / 306 / 318), prune3
consistency 100 %, per-N histograms equal to the snapshot's, `idx` set exactly `0..n−1`,
no duplicate index, every row certified with a strictly positive recomputed gap.

Cache: 6449 entries, scale histogram `{26: 6446, 28: 3}`, all with a content-verified fresh
witness (file path + file sha256 + line number + source snapshot sha256).

## 4. Commands for the merged domain

```powershell
# 1. replay a manifest (own out-stem per slice; never share a writer)
py -3 -B py/verify_manifest.py --snapshot <MANIFEST.json> --out-stem <STEM> `
       --cache out/certified-cache.jsonl --expect-hash <SHA256 of MANIFEST.json>

# 2. interface check of that replay
py -3 -B py/check_results.py --snapshot <MANIFEST.json> --out-stem <STEM>

# 3. after adding new stems, register them, then rebuild provenance + witnesses
#    (add stem -> snapshot path in cache_provenance.STEM_SNAPSHOT / SOURCES first)
py -3 -B py/cache_provenance.py          # content-verified fresh ancestry, T1..T7
py -3 -B py/bind_fresh_provenance.py     # sidecar + in-place witness (needs no active writer)

# 4. promote new fresh verdicts into the production cache (atomic, strict)
py -3 -B py/migrate_cache.py
py -3 -B py/audit_existing_cache.py      # re-derive provenance of every entry + controls

# 5. final acceptance (frozen hashes; global only if pending is empty)
py -3 -B py/acceptance_check.py --snapshot <MANIFEST.json> --out-stem <STEM> --freeze
```

Rules that the tooling enforces by construction: unknown `N` is refused; a missing
`used_scale` is only accepted for the audited legacy files at the audited N/scale; a row
that came from the cache can never serve as its own fresh evidence; `pending ≠ 0` can never
produce a global certificate.

## 5. Frozen artefacts (sha256 truncated for display)

* `out/certified-cache.jsonl` — 6449 entries, `2c69fed4c561857f…`
* `out/cache-provenance.json` — 6449 verified, `fc67cbd8035d7c85…`
* `out/cache-fresh-witness.jsonl`, `out/fresh-source-register.json`
* `out/acceptance-final-wave-base.json`, `out/freeze-final-wave-base.json`
* archives: `archive/verify-stage11825.jsonl` (2529 fresh), `…-run1.jsonl`, `…-run2.jsonl`
  (3 fresh at scale 28), `archive/verify-merged-partial-frozen.jsonl`,
  `archive/verify-final-wave-base-frozen.jsonl`
* source drift for the run launched as PID 32088/15908: `out/source-hash-at-run32088.json`
  (only the disabled `--build-cache` path and the `--expect-hash` exit code changed; the
  replay arithmetic path was not touched).
