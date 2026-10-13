# SOURCE-CALL-CONTRACT — which kernel, which arguments, which screening

Purpose: pin down, by signature and by hash, that **every** fresh generation and every replay
in this scope calls the frozen integer kernel with the **screened** default, and that
`screen=False` (which the Lead's stress audit F3 found mathematically unsafe) is not used
anywhere.  This is a *call-site contract*, not a re-proof of the kernel.

## 1. The frozen artefacts

| artefact | sha256 | notes |
|---|---|---|
| `members/upper-audit/integer-atomic/py/integer_kernel.py` | `0115c3f3660382cc5bcc53c1faf287ff624ca2f2c649a02035b7494759c0fc50` | `IntAtoms(H, weights, Sexpt=26)` — N=2048 path |
| `members/upper-audit/integer-atomic/py/integer_kernel_n.py` | `a89a2cee8dcbcf4dd7585b6878a6ad48a2db6543c109473936e08096a7085d53` | `IntAtomsN(H, weights, vectors, Sexpt=26, screen=True)` |
| `…/evidence/canonical-unit-vectors-8192.json` | `e2fe3e7d6f0ab37587e83a9214b1abbe1127f8a83593732de1a584d88b7fb77a` | explicit 8192 vector set |
| `evidence/atomic-unit-vectors-2048.json` | `acc14b2c954c91748e38a0e78720d717de8f45ce17456d4f121dc6a4c1085481` | explicit 2048 vector set |

Constructor signature, read from the frozen file:

```
IntAtomsN.__init__(self, H, weights, vectors, Sexpt=26, screen=True)
IntAtoms.__init__(self, H, weights, Sexpt=26)
```

`screen` is therefore **True by default**, and it is the default that all call sites below
rely on.  The only textual occurrences of `screen` in `integer_kernel_n.py` are the parameter
declaration and the `if screen:` branch.

## 2. Every call site, with its effective `screen`

| site | file:line | call | effective `screen` |
|---|---|---|---|
| producer dense fallback (8192) | `lead/hubline_domain.py:65` | `IntAtomsN(B, dense['weights'], vectors, Sexpt=26)` | **True** (default) |
| replay, N=2048 | `members/finite-reduction/integer-domain/py/verify_manifest.py:583` | `IK.IntAtoms(H, W, scale)` | n/a (no screen parameter) |
| replay, N=8192 | `members/finite-reduction/integer-domain/py/verify_manifest.py:590` | `_IKN.IntAtomsN(H, W, vectors_path(8192), Sexpt=scale)` | **True** (default) |

Repo-wide search for an explicit disabling (scope: the files present in the tree at the time
of writing — this is an inspection of current call sites, **not** a logical proof about every
historical execution):

```
grep -n "screen\s*=\s*False"  over all *.py in research-2026/n12-global  ->  NO MATCHES
```

So no call site in the current tree disables screening — neither in the producer, nor in the
replay, nor in any diagnostic script here.  The Lead's F3 finding
(`IntAtomsN(screen=False)` is mathematically unsafe, because without the screening step the
capture bound is not valid) therefore cannot be reached from any current call site.  The
positive evidence for the recorded verdicts is the pair (*actual fresh call contracts* +
*hash-bound kernel defaults*): every fresh computation in this scope went through
`IntAtoms`/`IntAtomsN` at the hashes in section 1 with `Sexpt` passed explicitly, and the
`screen` argument was never supplied, so the hashed default `True` applied.

## 3. What is *not* accepted as evidence

* **F1 — producer-stored boxes.**  A manifest leaf may carry `result` = the producer's own
  `certify()` output.  That field is **never** accepted as a certificate here.  The replay
  recomputes with its own `certify()` call and records the producer value only as a
  diagnostic (`diagnostic_recorded_status`, `diagnostic_agrees_recorded`); the acceptance
  gate (`acceptance_check.py`) reads `boxes`/`max_capture`/`demand`/`gap` from the **replay**
  row and requires `gap == demand − 10·max_capture > 0` there.  A disagreement between the
  producer's stored box count and the replay's box count is therefore visible but never
  load-bearing (the fresh-generation LP/atomic proposals are repaired by the producer, and
  the acceptance explicitly uses the integer kernel, as the producer's own comment states).
* **Cache rows that came from cache.**  Never used as their own fresh evidence; see
  `cache_provenance.py` (T1–T7 content verification against an immutable row file).

## 4. Scale is a stored property, never a substitute

`Sexpt` is passed explicitly (26 by default, 28 on escalation) and recorded per row as
`used_scale`; the cache key binds it.  A scale-26 certificate is reused as a **scale-26**
certificate and never presented as scale-28.  The three leaves that required escalation are
documented with full H/W/units/kernel/snapshot evidence in
`out/escalated-scale28-evidence.json`.

## 5. Honest dependency note for the acceptance gate

`acceptance_check.py` A3 compares the provenance record's numeric fields (`n`, `scale`,
`demand`, `max_capture`, `gap`) with the row.  Equality of the remaining identifiers
(`units`, `kernel`, `kernel_n`, full `h_sha`/`w_sha`) is **not** re-listed in A3 because it is
already established by A2: A2 re-derives the content key from the *current* snapshot leaf —
`content_key(H, W, N, vector-set hash, kernel hash, N-kernel hash, scale)` — and requires the
row's stored key to equal it **and** to be a member of the provenance verified set.  A key
that binds those ingredients cannot be shared by rows differing in any of them.  Stated
plainly: A3's field comparison is numeric-only; the identifier binding comes from A2 plus the
`cache_provenance.py` source audit.  Neither A2 nor A3 is an independent re-derivation of the
integer arithmetic.
