"""Merge + independent verification of the parallel-domain branch outputs.

FIXED CONVENTIONS (supersede the first version of this file):
  * the pending count of a branch is taken from its FRONTIER
    (info['n_pending']), never from the worker's counts dict, which has no
    'pending' key; the aggregate is asserted equal to len(final_pending);
  * the plan is re-verified by plan_branches.check_plan, i.e. by comparing the
    actual snapshot bytes/hash, each pending hash, root containment in its
    parent, exact canonical coverage per parent, cross-root disjointness and
    volume - not merely by a partition/volume spot check;
  * every file is read exactly once into `raw`, and all hashes reported for it
    are sha256(raw); no re-read of a path after parsing (provenance/race);
  * `export` writes a merged manifest in the ORIGINAL domain-manifest format
    (status/domain/counts/pending/leaves/hashes) into this members directory,
    and refuses unless every structural check passed; pending may be non-empty,
    in which case the exported status stays 'partial'.  A full-domain claim
    still requires the atomic replay by the lead.

Usage:
  py -3 merge_branches.py <plan.json> <branch0.json> ... [--out m.json]
  py -3 merge_branches.py --export <plan.json> <branch0.json> ... [--out f.json]
"""
import hashlib
import json
import sys
from pathlib import Path
from fractions import Fraction as F

import boxlib as BX
import plan_branches as PB


def _sha(raw):
    return hashlib.sha256(raw).hexdigest()


def resolve_source(plan_path, plan):
    """Resolve plan.source.path for callers whose cwd is not the plan directory.

    A plan may record a path relative to the directory it was written in (e.g.
    "reshard-base.json").  Try it as given, then relative to the plan file's
    directory.  The snapshot hash check inside check_plan still binds the bytes
    of whatever file is found, so resolving to another location cannot silently
    substitute a different snapshot."""
    raw = plan.get("source", {}).get("path")
    if not raw:
        return None
    if Path(raw).is_file():
        return str(raw)
    alt = Path(plan_path).parent / raw
    if alt.is_file():
        return str(alt)
    return raw


def load_plan(path):
    raw = Path(path).read_bytes()            # single read
    return json.loads(raw), _sha(raw)


def verify_branch(path, plan, plan_sha, problems_out, want_payload=False):
    raw = Path(path).read_bytes()            # single read: provenance binding
    file_sha = _sha(raw)
    try:
        out = json.loads(raw)
    except Exception as exc:                 # torn write window
        problems_out.append("%s: unparsable (%s)" % (path, exc))
        return None
    probs = []
    if out.get("plan_sha256") not in (None, plan_sha):
        probs.append("plan hash mismatch")
    if out.get("base_sha256") != plan["source"]["sha256"]:
        probs.append("base/snapshot hash mismatch (got %r)"
                     % out.get("base_sha256"))
    if not out.get("worker_sha256"):
        probs.append("worker_sha256 missing")
    bid = out.get("branch_id")
    ent = [b for b in plan["branches"] if b["id"] == "b%02d" % int(bid)] \
        if isinstance(bid, int) else [b for b in plan["branches"]
                                      if b["id"] == bid]
    if len(ent) != 1:
        probs.append("unknown/ambiguous branch id %r" % (bid,))
        problems_out += ["%s: %s" % (path, x) for x in probs]
        return None
    ent = ent[0]
    root = BX.decode(ent["root"])
    if "branch_root" not in out:
        probs.append("branch_root missing (metadata write window?)")
    else:
        if BX.encode(BX.decode(out["branch_root"])) != BX.encode(root):
            probs.append("branch_root != plan root")
        if out.get("parent_pending_index") != ent["parent_index"]:
            probs.append("parent_pending_index %r != plan %r"
                         % (out.get("parent_pending_index"),
                            ent["parent_index"]))
    leaves = out.get("leaves", [])
    pend = out.get("pending", [])
    frontier = [(BX.decode(lf["H"]), lf.get("type")) for lf in leaves]
    frontier += [(BX.decode(H), "pending") for H in pend]
    ok, why, stats = BX.check_frontier(root, frontier)
    if not ok:
        probs.append("frontier tree: %s" % why)
    n_at = sum(1 for _, t in frontier if t == "atomic")
    n_in = sum(1 for _, t in frontier if t == "infeasible")
    n_pe = sum(1 for _, t in frontier if t == "pending")
    c = out.get("counts", {})
    if c.get("certified") != n_at:
        probs.append("counts.certified %r != #atomic %d"
                     % (c.get("certified"), n_at))
    if c.get("infeasible") != n_in:
        probs.append("counts.infeasible %r != #infeasible %d"
                     % (c.get("infeasible"), n_in))
    if c.get("pending") not in (None, n_pe):
        probs.append("counts.pending %r != #pending %d"
                     % (c.get("pending"), n_pe))
    n_split = count_internal(root, frontier)
    if n_split is None:
        probs.append("cannot count internal nodes")
    else:
        if c.get("split") != n_split:
            probs.append("counts.split %r != internal nodes %d"
                         % (c.get("split"), n_split))
        if c.get("processed") != (n_split or 0) + n_at + n_in:
            probs.append("counts.processed %r != split+leaves %d"
                         % (c.get("processed"), (n_split or 0) + n_at + n_in))
    problems_out += ["%s: %s" % (path, x) for x in probs]
    info = dict(path=str(path), sha256=file_sha, id=bid, counts=c,
                status=out.get("status"), root_enc=BX.encode(root),
                pending_boxes=[BX.encode(BX.decode(H)) for H in pend],
                n_frontier=len(frontier), n_atomic=n_at, n_infeasible=n_in,
                n_pending=n_pe, n_split=n_split)
    if want_payload:
        info["_leaves"] = leaves
        info["_pending"] = pend
    return info


def count_internal(root, frontier, max_depth=400):
    fset = {BX.box_str(b) for b, _ in frontier}
    cnt = [0]

    def rec(B, depth):
        if depth > max_depth:
            return False
        if BX.box_str(B) in fset:
            return True
        c1, c2 = BX.split_box(B)
        cnt[0] += 1
        return rec(c1, depth + 1) and rec(c2, depth + 1)

    return cnt[0] if rec(root, 0) else None


def merge(plan_path, branch_paths, want_payload=False):
    plan, plan_sha = load_plan(plan_path)
    problems = []
    # ---- full independent re-verification of the plan against the snapshot
    src_used = resolve_source(plan_path, plan)
    plan_problems, snap = PB.check_plan(plan, src_used)
    problems += ["plan: %s" % x for x in plan_problems]
    planned = {b["id"]: b for b in plan["branches"]}
    roots = [BX.decode(b["root"]) for b in plan["branches"]]
    infos, seen = [], {}
    for p in branch_paths:
        info = verify_branch(p, plan, plan_sha, problems,
                            want_payload=want_payload)
        if info is None:
            continue
        key = "b%02d" % int(info["id"]) if isinstance(info["id"], int) \
            else info["id"]
        if key in seen:
            problems.append("branch %s supplied twice (%s, %s)"
                            % (key, seen[key], p))
            continue
        seen[key] = p
        infos.append(info)
    missing = sorted(set(planned) - set(seen))
    unknown = sorted(set(seen) - set(planned))
    if missing:
        problems.append("missing branches: %s" % ",".join(missing))
    if unknown:
        problems.append("unknown branches: %s" % ",".join(unknown))
    # ---- aggregate: pending comes from the FRONTIER, never from counts
    agg = dict(processed=0, split=0, certified=0, infeasible=0, pending=0)
    for i in infos:
        for k in ("processed", "split", "certified", "infeasible"):
            agg[k] += int(i["counts"].get(k, 0) or 0)
        agg["pending"] += int(i["n_pending"])
    final_pending = [p for i in infos for p in i["pending_boxes"]]
    assert agg["pending"] == len(final_pending), \
        "pending aggregate %d != frontier length %d" % (agg["pending"],
                                                        len(final_pending))
    if agg["pending"] != len(final_pending):
        problems.append("pending aggregate inconsistent with frontier")
    old = snap.get("counts", {})
    # ---- structural (shard) splits: DERIVED, never hardcoded.
    # Refining each source pending into its branch roots is a canonical binary
    # tree, so a pending with k roots contributes exactly k-1 internal nodes;
    # summing over pendings gives  sum(k_p - 1) = len(branches) - len(pendings).
    # For the stage11825 plan this is 11-8 = 3 and for the deep=0 plans it is 0,
    # which is why a constant 3 was wrong for deep=0 waves.
    per_pending = {}
    for b in plan.get("branches", []):
        per_pending[b["parent_index"]] = per_pending.get(b["parent_index"], 0) + 1
    shard_splits = sum(k - 1 for k in per_pending.values())
    if shard_splits < 0:
        problems.append("negative shard_splits (%d): plan has fewer branches "
                        "than pendings" % shard_splits)
    if len(per_pending) != len(snap["pendings"]):
        problems.append("shard_splits derivation: %d parents for %d pendings"
                        % (len(per_pending), len(snap["pendings"])))
    if shard_splits != len(planned) - len(snap["pendings"]):
        problems.append("shard_splits %d != branches - pendings = %d"
                        % (shard_splits, len(planned) - len(snap["pendings"])))
    v_old = sum(BX.volume(B) for B in snap["pendings"])
    v_new = sum(BX.volume(r) for r in roots)
    # ---- tree-count invariants (wave independent): for a forest of binary
    # trees, #internal = #leaves - #roots, so with the whole structure rooted at
    # the original box:   split = (atomic + infeasible + pending) - 1  and
    # processed = split + atomic + infeasible.  Checked on the SOURCE counts
    # (guards against a corrupted base propagating) and on the merged totals.
    def counts_ok(c):
        if not c:
            return None, "no counts"
        if not all(k in c for k in ("processed", "split", "certified",
                                    "infeasible")):
            return None, "counts incomplete"
        leaf = int(c["certified"]) + int(c["infeasible"]) + int(c.get("pending", 0))
        if int(c["split"]) != leaf - 1:
            return False, ("split %s != atomic+infeasible+pending-1 = %d"
                           % (c["split"], leaf - 1))
        if int(c["processed"]) != int(c["split"]) + int(c["certified"]) \
                + int(c["infeasible"]):
            return False, ("processed %s != split+leaves = %d"
                           % (c["processed"], int(c["split"])
                              + int(c["certified"]) + int(c["infeasible"])))
        return True, "ok"

    snap_ok, snap_why = counts_ok(dict(old, pending=len(snap["pendings"]))
                                  if old else None)
    if snap_ok is False:
        problems.append("source/base counts inconsistent: %s" % snap_why)
    totals = dict(
        processed=int(old.get("processed", 0)) + shard_splits + agg["processed"],
        split=int(old.get("split", 0)) + shard_splits + agg["split"],
        certified=int(old.get("certified", 0)) + agg["certified"],
        infeasible=int(old.get("infeasible", 0)) + agg["infeasible"],
        pending=agg["pending"])
    tot_ok, tot_why = counts_ok(totals)
    if tot_ok is False:
        problems.append("merged totals inconsistent: %s" % tot_why)
    # per-branch split check: branch internal nodes must also satisfy the
    # forest identity split = atomic + infeasible + pending - 1 for its own root
    for i in infos:
        c = i["counts"]
        if c.get("split") is not None:
            leaf = int(i["n_atomic"]) + int(i["n_infeasible"]) + int(i["n_pending"])
            if int(c["split"]) != leaf - 1:
                problems.append("branch %s: split %s != frontier-1 = %d"
                                % (i["id"], c["split"], leaf - 1))
    full = (not problems) and len(final_pending) == 0 \
        and len(infos) == len(planned)
    manifest = dict(
        schema="n12-merge-manifest/v1",
        plan=dict(path=str(plan_path), sha256=plan_sha,
                  branches=len(planned)),
        source=dict(plan["source"], resolved=src_used),
        branches=[{k: i[k] for k in ("path", "sha256", "id", "counts",
                                     "status", "n_frontier", "n_atomic",
                                     "n_infeasible", "n_pending", "n_split")}
                  for i in infos],
        replaced_pending=len(snap["pendings"]),
        final_pending=sorted(final_pending),
        counts=dict(
            old=old,
            shard_splits=shard_splits,
            shard_splits_derivation="sum over source pendings of (roots-1) = "
                                    "branches - pendings = %d - %d"
                                    % (len(planned), len(snap["pendings"])),
            per_pending_roots=per_pending,
            source_counts_check=(None if snap_ok is None else snap_ok),
            source_counts_note=snap_why,
            totals_check=(None if tot_ok is None else tot_ok),
            totals_note=tot_why,
            branches_sum=agg,
            totals=totals),
        volume=dict(old_pending=str(v_old), branch_roots=str(v_new),
                    equal=(v_old == v_new)),
        status=("certified-full-domain" if full else "partial"),
        problems=problems)
    if want_payload:
        manifest["_payload"] = dict(
            snapshot=snap["doc"],
            branches=[dict(path=i["path"], sha256=i["sha256"],
                           leaves=i["_leaves"], pending=i["_pending"])
                      for i in infos])
    return manifest


def export(plan_path, branch_paths, out_path):
    """Write a merged manifest in the ORIGINAL domain-manifest format.

    Refuses unless every structural check has passed; pending boxes are copied
    through and force status 'partial'.  The old snapshot's leaves are copied
    verbatim and each branch contributes only its own new leaves, so no leaf is
    duplicated (branch roots lie inside distinct old pendings, and old leaves
    lie outside every old pending).
    """
    man = merge(plan_path, branch_paths, want_payload=True)
    if man["problems"]:
        return dict(exported=False, problems=man["problems"])
    pay = man["_payload"]
    snap_doc = pay["snapshot"]
    leaves = list(snap_doc.get("leaves", []))
    pending = []
    for b in pay["branches"]:
        leaves.extend(b["leaves"])
        pending.extend(b["pending"])
    t = man["counts"]["totals"]
    doc = dict(
        status="certified full domain" if not pending else "partial",
        domain=snap_doc.get("domain"),
        counts=dict(processed=t["processed"], split=t["split"],
                    certified=t["certified"], infeasible=t["infeasible"]),
        pending=pending,
        leaves=leaves,
        hashes=dict(source=man["source"]["sha256"],
                    plan=man["plan"]["sha256"],
                    branches={("b%02d" % int(b["id"])) if isinstance(b["id"], int)
                              else b["id"]: b["sha256"]
                              for b in man["branches"]},
                    merger=_sha(Path(__file__).read_bytes())),
        provenance=dict(kind="sharded-merge",
                        source_manifest=man["source"]["path"],
                        plan=man["plan"]["path"],
                        branch_files=[b["path"] for b in man["branches"]],
                        shard_splits=man["counts"]["shard_splits"],
                        note=("structural merge only; a full-domain claim "
                              "still requires the atomic replay")))
    Path(out_path).write_text(json.dumps(doc, indent=1), encoding="utf8")
    return dict(exported=True, path=str(out_path), status=doc["status"],
                leaves=len(leaves), pending=len(pending),
                counts=doc["counts"],
                sha256=_sha(Path(out_path).read_bytes()))


def main():
    argv = list(sys.argv[1:])
    want_export = "--export" in argv
    argv = [a for a in argv if a != "--export"]
    out = "merge-manifest.json"
    if "--out" in argv:
        i = argv.index("--out")
        out = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    if len(argv) < 2:
        print(__doc__)
        return
    if want_export:
        print(json.dumps(export(argv[0], argv[1:], out), indent=1))
        return
    man = merge(argv[0], argv[1:])
    Path(out).write_text(json.dumps(man, indent=1), encoding="utf8")
    print(json.dumps({"status": man["status"],
                      "counts": man["counts"]["totals"],
                      "volume_equal": man["volume"]["equal"],
                      "final_pending": len(man["final_pending"]),
                      "problems": man["problems"]}, indent=1))
    print("wrote", out)


if __name__ == "__main__":
    main()
