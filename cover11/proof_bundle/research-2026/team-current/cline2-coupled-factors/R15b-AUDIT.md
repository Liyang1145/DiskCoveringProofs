# R15b audit — C859 assembly: constant, partition, applicability, hashes

Scope: own files only.  I did **not** rerun the 22 factors and did **not** optimize any
coefficient.  The audit re-evaluates the lead's published numbers from the recorded uppers
and the frozen file, and checks the claims of `lead/LOCAL-Q0-FLAT-EXCLUSION.md` and
`lead/assemble_current_patch.py`.

## 1. Exact constant from atom matching — agrees to all published digits

Two independent evaluations of the constant (60 dps; and an exact rational for the
coefficient part):

* **Coefficient-level (exact rational).** The signed coefficient sum of the constant block is
  `-1865395217/250000000 = -7.461580868` exactly, so `pi * that = -23.44124763907495274818
  8621601385129817276418730132340749262064852…` — an exact rational times pi.
* **Factor-level.** `const + sum22 + 28.1044 =`
  `[3.138947237817163670369698456766837129703464047536194960119006519,
    3.138947237817163670369698456766837129703464047536194960119038787]`
  and `pi - total` = `0.00264541577262956809294492651266575449370535183891086085592…`.

The lead's published `constant+sum22 ∈ [-24.965452762182836329630301543233162870298784,
-24.9654527621828363296303015432331628702947432]` and margin `0.00264541577` reproduce
**exactly**.  The sub-`4e-39` endpoint spread is **precision only**: the lead's assembly
parses each recorded upper exactly (`iv.mpf(d['upper'])` — the binary float read exactly;
there is **no 9-decimal rounding of the upper records**; only the `z` coefficients are
9-decimal literals).  `strictly below pi = True`.

Interface-consistency cross-check: my independently computed 22-term float sum
`-1.5242051231078835` matches the float of the exact binary sum
`-112466487287232356015/73786976294838206464` bit-for-bit, so the interval endpoints and the
float aggregation are mutually consistent.

## 2. Index partition 7 + 22 — complete and disjoint

```
skipped (C854)  : [1, 2, 12, 13, 21, 22, 23]                                    (7)
assembled (22)  : [0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19,
                   20, 24, 25, 26, 27, 28]                                      (22)
overlap         : []          union  = 0..28 exactly
```

Index identities from the kernel blocks (`certify_q0_closure.py:35-67` appends
`face0..face10`, `:68-75` appends `switch0..switch8`, `:76-108` appends `ring0..ring8`):
index **2 is `face2`**, and the only ring indices are 20..28.  Within the seven-block that
means index 2 is a face factor and index 22 is a ring factor — no duplicated switch.  The
partition is exact.  (An earlier version of this report wrongly called index 2 a ring
factor; corrected.)

## 3. Broad-domain applicability — supported

The 22 recorded uppers were produced with the kernel's unchanged domains:
face factors on `[0,π]² ∩ {a+b ≤ π}`, switch factors on `[0,π/2]`, ring factors on
`[0,π]×[0,1]²` with only the necessary C844 filter applied.  `lead/certify_q0_closure.py`
builds those three blocks on the full domain (lines 35–108) and applies no Q0 restriction.
So `LOCAL-Q0-FLAT-EXCLUSION.md` line 11 ("No 22 factor bound is restricted to Q0, so they
apply in particular to it") is supported: the bound is on the factor over its full domain,
hence also over the Q0 sub-box.

Two honest limits on that statement:
* **Pruning soundness.** The upper each factor reports is sound only because discarded boxes
  retain their uppers in `discarded`/`terminal max` and because `lower_probe` is used solely
  as a pruning comparator.  That property is a property of the certifier (constructor-verified)
  — it is not re-verified inside my 22 records.
* **Coverage.** The 22 factor domains are full, but that the 22 factors + the 7 cover the
  29-factor split is a **partition identity**, not a coverage-of-space statement.  No claim
  is made here that the Q0 complement is covered.

## 4. Source hashes and stale bytes — clean

* 22/22 records present, `digest-field mismatches = []`, no `*bound_*` file for an index
  outside the 22.
* Every one of the 22 records embeds **exactly one** digest hex, the current
  `5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb`; neither the v2
  (`a856f2c12bcc…`) nor the older (`adf07c491585…`) digest appears in any record.
* Canonical input hashes at audit time:
  `joint_nested_frozen.json 5671967c…8221fb`;
  `certify_joint_rest_tight.py 023f2dce4a7a63b7ae6fb537907e042255addeef1f81911c09106b9740105793`;
  `certify_q0_closure.py 901dca3e9c87c8dc6950ec90c5f300fd8ce62ff9341bbab932fb65e2de913e69`;
  `q0_exact_closure_radius.py c49c5df59b21c402888d00c045f6af98c56e72b784c578155809607ba352ca0a`;
  `q0_graphs.json 7d1a30178bf79100ff696970cb6121f4a2a9a984940bf9d2c4a4c8c7826b03ac`;
  `n11/upper/certified_object.json 15a127b2045d90288274bb07dbeae016144b66c6eba89bbf13c73350021ed820`.
  The C854 evidence file `local_ridge_upper.json` carries
  `coefficient_sha256 = 5671967c…8221fb`, matching.

## 5. Items raised, and their disposition after the lead's replies

Items 1, 4 and 6 were **doc/interface level only**; item 1 is now **fixed in this directory**,
items 2, 3 and 6 are **withdrawn** (my readings were wrong or over-cautious), item 5 stands as
a recorded scope note.

1. **[FIXED]** `summary.json` lacked a `source_hashes` field while `R15-SWEEP-RESULT.md`
   pointed at it.  Action taken: `rerun_joint_22.py` now writes both `source_hashes` (7
   entries: the frozen file under both names, the certifier, the kernel, the prep module,
   `q0_graphs.json`, `n11/upper/certified_object.json`) and `record_hashes` (SHA256 of each of
   the 22 records) into `summary.json`; regenerated via `--aggregate`.  The regenerated file
   is otherwise unchanged (`sum_of_present_uppers = -1.5242051231078835`,
   `sum_covers_all_22 = True`), and the 22 records were not touched.
2. **[WITHDRAWN — my error]** I claimed a constant-formula mismatch.  Kernel line 110 is
   exactly
   `total = pi*(sum(z[:9]) + 2*sum(z[9:11]) + sum(z[kap:lam]) - 2*z[lam] - 2*z[eta]) + 2*z[eta]*asin(2*R) - pi*sum(z[cl:])`,
   i.e. the `-2*z[eta]` sits **inside** the `pi` parenthesis and the `asin` term **outside**;
   the doc quotes this correctly (I had mis-transcribed it).  `assemble_current_patch.py:7`
   adds an extra `-2*z[72]` inside the `pi`, and the script **asserts `all(x==0 for x in
   z[50:73])` at line 6** before dropping the `asin` term, so there is no mismatch and no
   unreported assumption.  With `z[72] = 0` all forms coincide.
3. **[WITHDRAWN — my error]** C854 is an explicit `<= 28.1044` statement whose retained leaf
   upper `28.1043997462215…` differs deliberately; citing `28.1044` in C859 is therefore the
   proved quantity, not a conflation of two values.  Nothing to change.
4. **[OPTIONAL, offered]** A single aggregating hash for the 22 records.  The lead is pinning
   the 22 file hashes; `record_hashes` is now additionally available in `summary.json` in this
   directory.
5. **[STANDS as scope note]** `current_seven_split_control.json` carries only
   `coefficient_sha256`, `points = 676`, `max_error = 1.7763568394002505e-14` and a scope
   string — no points, no per-point residuals, no factor tags.  It is therefore not
   independently re-verifiable as stored, and it calibrates the **seven-atom** block only;
   the 22-atom interface has no control of that kind.  The doc already labels it a control
   and not the proof, which is correct.
6. **[WITHDRAWN — deliberate]** Running the full certifier in C859's `repro` line is
   intentional (it regenerates the 22 records rather than trusting stored ones).
   `--aggregate` remains available as a shortcut and can be added to the doc if wanted.

## 6. Verdict on the three requested items

| item | verdict |
|---|---|
| exact constant from atom matching/closure | **agrees to all published digits**; exact rational coefficient sum `-1865395217/250000000`; `pi−total = 0.0026454157726295680929449265…` |
| index partition 7 + 22 | **complete, disjoint, equals 0..28**; index 2 is `face2`, index 22 is `ring2`; no double count |
| broad-domain applicability | **supported** (full domains, C844-filtered rings only); pruning soundness and coverage are certifier/partition properties, not re-verified here |
| 22 source hashes / stale bytes | **clean**: 22/22, current digest only, no v2 or older bytes anywhere in the records; `source_hashes` and `record_hashes` now recorded in `summary.json` |

No arithmetic discrepancy found.  The bound and the conclusion
`3.138947237817163670369698456766837129705605… < pi` are unaffected by any item above.
