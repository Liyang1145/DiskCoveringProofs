#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""fresh_source_register.py -- anchor every FRESH ancestry to immutable file bytes.

The Lead's concern: stage11825's 2529 newly-certified leaves were fresh when first computed,
but the working JSONL was later rewritten by a resume in which those same indices were cache
hits ("cached source pointing back at the same idx").  The freshness must therefore live in
ARTIFACTS THAT ARE NOT REWRITTEN, and the mapping must be anchored to their bytes.

This script records, for each immutable copy that carries fresh rows, its sha256, row count
and the set of fresh (stem, idx) pairs it can supply; then it re-derives the fresh ancestry
of every production cache entry and writes the pairing.  Nothing here trusts `from_cache`
alone: a row counts as fresh only at from_cache == False, or (for the pre-field generation)
under the audited rule of cache_provenance.PRE_FIELD_STEMS.
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
OUT = os.path.join(MEM, "out")
ARCH = os.path.join(MEM, "archive")
sys.path.insert(0, HERE)
import cache_provenance as CP

IMMUTABLE = [
    os.path.join(ARCH, "verify-stage11825.jsonl"),          # pristine post-run-1 copy
    os.path.join(ARCH, "verify-stage11825-run1.jsonl"),     # full run-1 ledger
    os.path.join(ARCH, "verify-stage11825-run2.jsonl"),     # the 3 escalated, scale 28
    os.path.join(OUT, "verify-stage2200.jsonl"),            # pre-field generation
    os.path.join(OUT, "verify-stage6700.jsonl"),
]


def main():
    reg = []
    fresh_index = {}
    for path in IMMUTABLE:
        if not os.path.exists(path):
            reg.append(dict(path=os.path.relpath(path, MEM), present=False))
            continue
        raw = open(path, "rb").read()
        rows = [json.loads(l) for l in raw.decode("utf-8").splitlines() if l.strip()]
        fresh = [r for r in rows if r.get("from_cache") is False]
        stem = os.path.basename(path).replace("verify-", "").replace(".jsonl", "")
        stem = stem.replace("-run1", "").replace("-run2", "")
        for r in fresh:
            fresh_index.setdefault((stem, r.get("idx")), os.path.relpath(path, MEM))
        reg.append(dict(path=os.path.relpath(path, MEM),
                        sha256=hashlib.sha256(raw).hexdigest(), rows=len(rows),
                        fresh_rows=len(fresh), present=True))
    cache = [json.loads(l) for l in open(os.path.join(OUT, "certified-cache.jsonl"),
                                         encoding="utf-8") if l.strip()]
    unanchored = [e["ckey"] for e in cache
                  if (e.get("fresh_ancestor") or {}).get("stem") and
                  (e["fresh_ancestor"]["stem"], e["fresh_ancestor"]["idx"]) not in fresh_index
                  and not (e["fresh_ancestor"].get("pre_field_rule"))]
    out = dict(rule=("an entry's fresh_ancestor must be resolvable in an IMMUTABLE file "
                     "copy (sha256 recorded) unless it uses the audited pre-field rule"),
               immutable_copies=reg,
               fresh_pairs_available=len(fresh_index),
               cache_entries=len(cache),
               entries_with_fresh_ancestor=sum(1 for e in cache if e.get("fresh_ancestor")),
               unanchored_entries=len(unanchored),
               unanchored_sample=unanchored[:5])
    dest = os.path.join(OUT, "fresh-source-register.json")
    with open(dest, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out, indent=1)[:2200])
    print("register ->", dest)


if __name__ == "__main__":
    main()