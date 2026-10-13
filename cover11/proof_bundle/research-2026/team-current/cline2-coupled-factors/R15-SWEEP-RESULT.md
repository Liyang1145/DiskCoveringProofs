# R15 result — corrected 22-factor sweep under the current frozen coefficients

One pass, existing per-factor budget, no precision or grid increase.  Outputs in this
directory only; the lead directory was not written to (its recent files are the lead's own
concurrent work, not mine).

## 1. Pre-launch audit (requested before launch) — PASS

Source hashes captured at launch, as read from the lead files:

```
5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb  joint_nested_frozen.json
5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb  joint_patch_frozen_v2.json (stale name, CURRENT bytes)
023f2dce4a7a63b7ae6fb537907e042255addeef1f81911c09106b9740105793  certify_joint_rest_tight.py
901dca3e9c87c8dc6950ec90c5f300fd8ce62ff9341bbab932fb65e2de913e69  certify_q0_closure.py
c49c5df59b21c402888d00c045f6af98c56e72b784c578155809607ba352ca0a  q0_exact_closure_radius.py
7d1a30178bf79100ff696970cb6121f4a2a9a984940bf9d2c4a4c8c7826b03ac  q0_graphs.json
15a127b2045d90288274bb07dbeae016144b66c6eba89bbf13c73350021ed820  n11/upper/certified_object.json
```

**How the `__file__` alias resolves (verified, not assumed).** The certifier is invoked as
`./certify_joint_rest_tight.py` with `cwd = alias`, so its `Path(__file__).parent` is the
alias dir; line 8 sets `ns={'__file__': str(P/'certify_q0_closure.py')}` — also the alias;
the kernel's own line 7 then takes `Path(__file__).parent` and reads
`P/'joint_patch_frozen_v2.json'` — the alias copy, i.e. the **new** bytes.  The kernel's
sibling `q0_graphs.json` resolves through the same alias parent, and the repo-relative
`n11/upper/certified_object.json` resolves through `cwd`.

Audit verdict (six paths, each compared byte-for-byte against its lead source):
**all byte-identical, PASS**; the kernel coefficient path holds sha256 `5671967c5a3df341…`
equal to the canonical file; the kernel-consumed `z[:3]` equals the canonical `z[:3]`.

## 2. Sweep result

```
records = 22 / 22        digest mismatches = 0        missing = []
budget_ended = False for every factor
total evaluations = 283 236        max per factor = 109 329   (cap 240 000)
sum of the 22 factor uppers = -1.5242051231078835
```

Per factor (`upper`; all `digest_ok = True`):

| fi | factor | upper | fi | factor | upper |
|---|---|---|---|---|---|
| 0 | face0 | 0.3413027967429324 | 17 | switch6 | 1.9817239190319613e-05 |
| 3 | face3 | 0.33911062922752655 | 18 | switch7 | 0.13020305920540254 |
| 4 | face4 | -0.2603453981107087 | 19 | switch8 | 1.9853416430433903e-05 |
| 5 | face5 | -0.016982176657950928 | 20 | ring0 | -0.548677388561477 |
| 6 | face6 | -0.05335241614363209 | 24 | ring4 | -0.5571787901629601 |
| 7 | face7 | -0.016951217443736778 | 25 | ring5 | -0.45520995848631624 |
| 8 | face8 | -0.2603454622120701 | 26 | ring6 | -0.05475261592029134 |
| 9 | face9 | 0.16107808114822725 | 27 | ring7 | -0.10161960645889918 |
| 10 | face10 | 0.16018700972299357 | 28 | ring8 | -0.4601111095399978 |
| 11 | switch0 | 2.0002210378923662e-05 | 14 | switch3 | 1.9951263031208914e-05 |
| 15 | switch4 | 1.9717507446096554e-05 | 16 | switch5 | 0.1293400989065974 |

Everything is in `out/r15_5671967c5a3d/` (`joint_patch_tight_bound_<i>.json`,
`summary.json` including the source-hash block, `summary.md`), with the run log in
`out/r15_sweep.log`.  The alias was removed.

## 3. The 29-factor split, stated without conflation

```
factor 0..10   face0..face10        (11)
factor 11..19  switch0..switch8      (9)
factor 20..28  ring0..ring8          (9)
                                     --
                                     29

C854-covered (skipped by the certifier) : {1, 2, 12, 13, 21, 22, 23}   (7)
recomputed here                          : {0, 3, 4, 5, 6, 7, 8, 9, 10, 11,
                                            14, 15, 16, 17, 18, 19, 20,
                                            24, 25, 26, 27, 28}        (22)
29 = 7 + 22, complete and disjoint.
```

**Two separate quantities, never to be conflated:**

* **LOCAL patch (conditional, Q0 ridge box only):** `28.10439974622152` — C854, valid only
  for `r∈[.379,.38], b1∈[1.106,1.108], b2∈[1.068,1.071], delta∈[.035,.040]`, all width
  fibers, 0 live boxes.
* **ENTIRE patch, currently loose:** `28.315358592526042` (value as given by the lead).

`sum of the 22 recomputed factors = -1.5242051231078835` is the second component of the
29-factor split.  I do **not** claim this sum bounds the patch, I do **not** claim the Q0
complement is covered, and I do **not** claim a sharp global bound or a flat-sector-2
exclusion.  The exact identity that assembles the 22 `upper`s into a patch-level upper
bound (and the constant offset, if any) is outside my scope and is not verified here — the
22 factor values are sound interval uppers, but no statement is made about how the lead's
assembly combines them.

## 4. Diagnostic relevant to the lead's allocation question

Numerically at hand (no interpretation beyond arithmetic):

* local Q0 (`28.10439974622152`) and the entire patch as loose (`28.315358592526042`) differ
  by `0.210958846304522`;
* each of the 22 remaining factor uppers is bounded by `max = 0.3413027967429324`
  (face0), and the largest-magnitude entry overall is `-0.5571787901629601` (ring4);
* dividing the two: `0.210958846304522 / 0.3413027967429324 = 0.6181`, i.e. **one**
  remaining factor's typical magnitude (about `0.30–0.34` for the two faces that matter)
  already accounts for roughly `1.5×` the entire local-to-loose gap.

Read-off: the 22-block is not a small residual relative to that gap; per-factor magnitudes
in the block exceed the gap, so if the patch-level bottle neck is the local Q0 term then
re-allocating effort within the 22 block cannot close the `0.211` on its own, whereas two
factors of the block carry comparable magnitude.  This is arithmetic on the given numbers,
not a proof about either bound.
