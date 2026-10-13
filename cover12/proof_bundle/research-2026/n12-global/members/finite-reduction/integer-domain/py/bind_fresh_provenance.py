#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""bind_fresh_provenance.py -- write the CONTENT-VERIFIED fresh witness into each entry.

cache_provenance.py has already established, per entry, a fresh terminal row satisfying
T1..T7 (source snapshot hash, leaf H/W/N, vector set, kernel hashes, scale, gap arithmetic).
This script copies that witness -- including the immutable FILE path, its sha256 and the
line number -- into the cache entry, so a downstream reader never has to re-walk a chain or
trust a bare `from_cache` flag.

It refuses to bind anything that did not pass T1..T7 (the provenance file must have failed=0).
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
OUT = os.path.join(MEM, "out")
CACHE = os.path.join(OUT, "certified-cache.jsonl")
PROV = os.path.join(OUT, "cache-provenance.json")


def main():
    prov = json.loads(open(PROV, encoding="utf-8").read())
    if prov.get("failed"):
        raise SystemExit("refusing to bind: cache-provenance.json reports %d unverified "
                         "entries" % prov["failed"])
    witness = {v["ckey"]: dict(fresh_file=v["fresh_file"],
                               fresh_file_sha256=v["fresh_file_sha256"],
                               fresh_line=v["fresh_line"], fresh_idx=v["fresh_idx"],
                               fresh_stem=v["fresh_stem"],
                               source_snapshot_sha256=v["snapshot_sha256"],
                               pre_field_rule=v["pre_field_rule"],
                               chain_depth=v["chain_depth"])
               for v in prov["verified"]}
    entries = [json.loads(l) for l in open(CACHE, encoding="utf-8") if l.strip()]
    bound, unbound = 0, []
    for e in entries:
        w = witness.get(e["ckey"])
        if w is None:
            unbound.append(e.get("ckey"))
            continue
        e["verdict_witness"] = w
        e["fresh_ancestor"] = dict(stem=w["fresh_stem"], idx=w["fresh_idx"],
                                   file=w["fresh_file"],
                                   file_sha256=w["fresh_file_sha256"],
                                   line=w["fresh_line"])
        bound += 1
    # sidecar first: a running verifier holds the cache open for append, which on Windows
    # blocks an atomic replace.  The sidecar is keyed by ckey and is equally auditable.
    side = os.path.join(OUT, "cache-fresh-witness.jsonl")
    with open(side, "w", encoding="utf-8") as f:
        for k in sorted(witness):
            f.write(json.dumps(dict(ckey=k, **witness[k])) + "\n")
    tmp = CACHE + ".tmp"
    in_place, deferred_reason = False, None
    with open(tmp, "w", encoding="utf-8") as f:
        for e in entries:
            f.write(json.dumps(e) + "\n")
    try:
        os.replace(tmp, CACHE)
        in_place = True
    except PermissionError as ex:
        deferred_reason = ("cache is open by a running verifier (%s); witness is in the "
                           "sidecar and must be bound after the run exits" % ex.__class__.__name__)
        try:
            os.remove(tmp)
        except OSError:
            pass
    out = dict(entries=len(entries), witness_bound=bound, unbound=len(unbound),
               unbound_sample=unbound[:5], sidecar=os.path.relpath(side, MEM),
               bound_in_place=in_place, deferred_reason=deferred_reason,
               note="witness includes immutable file path, file sha256 and line number")
    if in_place:
        # Writing the cache changes its BYTES, so any provenance computed earlier records a
        # stale cache_sha256.  Re-run provenance here, so the recorded cache hash is always
        # the hash of the bytes on disk (the acceptance gate demands byte equality).
        import cache_provenance as CP
        print("re-running provenance so cache_sha256 matches the bound bytes ...")
        CP.main()
        prov2 = json.loads(open(PROV, encoding="utf-8").read())
        out["provenance_rerun_after_bind"] = dict(
            cache_sha256=prov2.get("cache_sha256"),
            verified=prov2.get("verified_fresh"), failed=prov2.get("failed"))
    with open(os.path.join(OUT, "fresh-witness-binding.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out, indent=1))
    if unbound:
        raise SystemExit(1)


if __name__ == "__main__":
    main()