# Lane A CI evidence, run 40818062141

Source: public GitHub Actions artifact `n11-build-40818062141`, head
`a201da0d1ca99fc847495d7c84dc9f8da0faa7c3`, created 2026-10-29T10:05:02Z.
This is an artifact audit, not a theorem proof.

## C450 targets: exit 0

```
N11Formalization.C450Source36Segment             0
N11Formalization.C450ChainCompletionEndpoint     0
N11Formalization.C450ChainCompletionTail         0
N11Formalization.C450ChainCompletionMid1         0
N11Formalization.C450ChainCompletionMid2         0
N11Formalization.C450ChainCompletionMid3         0
N11Formalization.C450ChainCompletion            0
N11Formalization.C450ChainCompletionMain        0
```

Therefore `C450ChainCompletion.h450` and the Main consumer built in CI at that
head.  Run 40815681024 also has job conclusion "success", but its artifact shows
all targets exit 1: job success is not build success because the workflow ends
with `true`.

## SevenClassQ0Deg3Cos at that head: exit 1

```
line 28:45 unsolved goals
line 100:9 typeclass instance problem is stuck
lines 112,113,114,117,122,133,142,163,164 Unknown identifier `nodeQ`
line 140:6 mod_cast has type ...
line 140:31 Application type mismatch
```

Fixes applied in session part 27 (module hash
`2adcd5d1154e71aca659639c88f4e462b937d7458d1c7c5516e7b8d6647959db`),
CI-pending.
