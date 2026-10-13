"""Branch sharding plan + plan verification for the k10 wrapper.

LOAD-BEARING API (use only these):
    plan   : py -3 plan_branches.py plan  <snapshot> <plan.json> [--deep K]
    check  : py -3 plan_branches.py check <snapshot> <plan.json>
    library: make_plan, check_plan, load_snapshot, and boxlib.*

The authoritative merge/export lives in merge_branches.py
(merge_branches.merge / merge_branches.export); handles the real worker format of
lead/run_domain_branch.py (branch_id int, branch_root, base_sha256,
worker_sha256, leaves/pending, counts without a 'pending' key) and binds every
reported hash to the single read of the file it parses.

DEPRECATED, NON-LOAD-BEARING (kept only so old callers do not break, both emit
DeprecationWarning on call and must not be used for the sharded merge):
    verify_branch_output(out, plan)   -> replaced by merge_branches.verify_branch
    merge(plan_path, branch_paths)    -> replaced by merge_branches.merge
    the module-global plan_sha256     -> legacy slot used by verify_branch_output
They spoke an older output schema ({"schema":"n12-branch-output/v1", frontier
with tags, root_sha256/plan_sha256/source_sha256 fields, ids "b00".."b10") and
aggregated the pending count from counts, which the worker does not provide.

Provenance rule (all live code): each file is read exactly once into `raw`; the
parsed object and every hash reported for it are derived from those same bytes.
"""

import hashlib
import json
import sys
from fractions import Fraction as F
from pathlib import Path

import boxlib as BX


SCHEMA_PLAN = "n12-branch-plan/v1"
SCHEMA_OUT = "n12-branch-output/v1"
SCHEMA_MERGE = "n12-merge-manifest/v1"


def load_snapshot(path):
    raw = Path(path).read_bytes()   # single read: the hash binds to these bytes
    d = json.loads(raw)
    pend = [BX.decode(H) for H in d.get("pending", [])]
    leaves = d.get("leaves", [])
    return dict(path=str(path), sha256=hashlib.sha256(raw).hexdigest(), doc=d,
                pendings=pend, leaves=leaves,
                counts=d.get("counts", {}), domain=d.get("domain"))


def make_plan(snapshot_path, deep=1):
    """deep = number of extra canonical splits applied to the largest pending."""
    snap = load_snapshot(snapshot_path)
    pendings = snap["pendings"]
    branches = []
    bid = 0
    refs = []
    for idx, P in enumerate(pendings):
        if idx == 0 and deep > 0:
            # canonical refinement tree of depth `deep` under this pending
            level = [P]
            pathhist = [[P]]
            for _ in range(deep):
                nxt = []
                for Q in level:
                    c1, c2 = BX.split_box(Q)
                    nxt.extend([c1, c2])
                pathhist.append(nxt)
                level = nxt
            for Q in level:
                branches.append(dict(id="b%02d" % bid, root=BX.encode(Q),
                                     root_sha256=BX.box_hash(Q),
                                     parent_pending=BX.encode(P),
                                     parent_index=idx, deep=deep))
                bid += 1
            refs.append(dict(pending=BX.encode(P), pending_sha256=BX.box_hash(P),
                             pending_index=idx, mode="split", depth=deep,
                             intermediate=[[BX.encode(Q) for Q in lvl]
                                           for lvl in pathhist[1:-1]],
                             branches=[b["id"] for b in branches
                                       if b.get("parent_index") == idx]))
        else:
            branches.append(dict(id="b%02d" % bid, root=BX.encode(P),
                                 root_sha256=BX.box_hash(P),
                                 parent_pending=BX.encode(P),
                                 parent_index=idx, deep=0))
            refs.append(dict(pending=BX.encode(P), pending_sha256=BX.box_hash(P),
                             pending_index=idx, mode="direct", depth=0,
                             intermediate=[],
                             branches=["b%02d" % bid]))
            bid += 1
    plan = dict(schema=SCHEMA_PLAN,
                source=dict(path=snap["path"], sha256=snap["sha256"]),
                domain=snap["domain"], tie_break="first widest dimension, "
                "midpoint split (lead/hubline_domain.py)",
                pending_count=len(pendings), branch_count=len(branches),
                count_snapshot=snap["counts"], refs=refs, branches=branches)
    return plan


def check_plan(plan, snapshot_path=None):
    problems = []
    if plan.get("schema") != SCHEMA_PLAN:
        problems.append("plan schema mismatch")
    src = plan.get("source", {})
    spath = snapshot_path or src.get("path")
    if spath and Path(spath).exists():
        # SINGLE read: load_snapshot returns the sha256 of exactly the bytes it
        # parsed, so the comparison below binds to that one read (no second
        # file_sha256(spath) read, which would race the parse).
        snap = load_snapshot(spath)
        if snap["sha256"] != src.get("sha256"):
            problems.append("snapshot hash mismatch")
    else:
        problems.append("snapshot not found: %s" % spath)
        return problems, dict(pendings=[], counts={}, doc={}, sha256=None,
                              path=spath)
    by_index = {}
    for b in plan.get("branches", []):
        by_index.setdefault(b["parent_index"], []).append(b)
    # every pending is represented, and its branches are an exact canonical
    # refinement of it
    if len(by_index) != len(snap["pendings"]):
        problems.append("branch parents %d != pendings %d"
                        % (len(by_index), len(snap["pendings"])))
    for idx, P in enumerate(snap["pendings"]):
        if BX.box_hash(P) != plan["refs"][idx]["pending_sha256"]:
            problems.append("pending %d hash mismatch" % idx)
        bs = by_index.get(idx, [])
        roots = [BX.decode(b["root"]) for b in bs]
        for b, r in zip(bs, roots):
            if BX.box_hash(r) != b["root_sha256"]:
                problems.append("branch %s root hash mismatch" % b["id"])
            if not BX.contains(P, r):
                problems.append("branch %s root not inside pending %d"
                                % (b["id"], idx))
        ok, why, stats = BX.check_frontier(P, [(r, b["id"])
                                              for r, b in zip(roots, bs)])
        if not ok:
            problems.append("pending %d: %s" % (idx, why))
        else:
            if stats["volume"] != BX.volume(P):
                problems.append("pending %d: branch volumes do not sum" % idx)
    # cross-branch disjointness
    allroots = [BX.decode(b["root"]) for b in plan.get("branches", [])]
    ok, why = BX.check_partition(allroots)
    if not ok:
        problems.append(why)
    # total volume over all branch roots equals the pending volume
    vp = sum(BX.volume(P) for P in snap["pendings"])
    vr = sum(BX.volume(r) for r in allroots)
    if vp != vr:
        problems.append("total pending volume %s != branch volume %s" % (vp, vr))
    return problems, snap


def verify_branch_output(out, plan):
    """DEPRECATED (non-load-bearing).  Superseded by
    merge_branches.verify_branch, which (a) takes a path and binds the reported
    hash to the same bytes it parses, (b) reads the pending count from the
    frontier, and (c) uses the plan ids 'b00'..'b10'.  Kept only so that old
    callers do not break; do NOT use it for the sharded merge."""
    import warnings
    warnings.warn("plan_branches.verify_branch_output is deprecated; use "
                  "merge_branches.verify_branch", DeprecationWarning,
                  stacklevel=2)
    problems = []
    if out.get("schema") != SCHEMA_OUT:
        problems.append("output schema mismatch")
    if out.get("plan_sha256") != plan_sha256:
        problems.append("branch %s: plan hash mismatch" % out.get("branch_id"))
    if out.get("source_sha256") != plan["source"]["sha256"]:
        problems.append("branch %s: source hash mismatch" % out.get("branch_id"))
    bid = out.get("branch_id")
    ent = [b for b in plan["branches"] if b["id"] == bid]
    if len(ent) != 1:
        return ["unknown branch id %r" % bid], None
    root = BX.decode(ent[0]["root"])
    if out.get("root_sha256") != BX.box_hash(root):
        problems.append("branch %s: root hash mismatch" % bid)
    frontier = [(BX.decode(e["H"]), e.get("type")) for e in out.get("frontier", [])]
    ok, why, stats = BX.check_frontier(root, frontier)
    if not ok:
        problems.append("branch %s frontier: %s" % (bid, why))
    c = out.get("counts", {})
    n_at = sum(1 for _, t in frontier if t == "atomic")
    n_in = sum(1 for _, t in frontier if t == "infeasible")
    n_pe = sum(1 for _, t in frontier if t == "pending")
    if len(frontier) != n_at + n_in + n_pe:
        problems.append("branch %s: bad frontier types" % bid)
    for key, val in (("atomic", n_at), ("infeasible", n_in), ("pending", n_pe)):
        if c.get(key) is not None and c.get(key) != val:
            problems.append("branch %s: count %s=%s but frontier has %d"
                            % (bid, key, c.get(key), val))
    vis = out.get("visited")
    if vis is not None:
        vboxes = [BX.decode(e["H"]) for e in vis]
        vkeys = [BX.box_str(b) for b in vboxes]
        if len(set(vkeys)) != len(vkeys):
            problems.append("branch %s: duplicate visited box" % bid)
        for b in vboxes:
            if not BX.contains(root, b):
                problems.append("branch %s: visited box outside root" % bid)
                break
        fset = {BX.box_str(b) for b, _ in frontier}
        vset = set(vkeys)
        if not fset <= vset:
            problems.append("branch %s: frontier not contained in visited" % bid)
        # closure: every visited box is frontier or has both canonical children
        n_split = 0
        for b in vboxes:
            k = BX.box_str(b)
            if k in fset:
                continue
            c1, c2 = BX.split_box(b)
            if BX.box_str(c1) not in vset or BX.box_str(c2) not in vset:
                problems.append("branch %s: visited box without canonical "
                                "children" % bid)
                break
            n_split += 1
        if c.get("split") is not None and c.get("split") != n_split:
            problems.append("branch %s: split count %s != internal nodes %d"
                            % (bid, c.get("split"), n_split))
    return problems, dict(root=root, stats=stats, counts=c,
                          frontier=frontier)


plan_sha256 = None    # LEGACY global, used only by the deprecated
                      # verify_branch_output below.  Non-load-bearing.


def merge(plan_path, branch_paths):
    """DEPRECATED (non-load-bearing).  This was the first, summary-only merge;
    it aggregated pending from counts and did not re-verify the plan.  The
    authoritative merge/export is merge_branches.merge / merge_branches.export.
    Kept only for old callers."""
    import warnings
    warnings.warn("plan_branches.merge is deprecated; use merge_branches.merge "
                  "or merge_branches.export", DeprecationWarning, stacklevel=2)
    global plan_sha256
    plan_sha256 = BX.file_sha256(plan_path)
    plan = json.loads(Path(plan_path).read_text())
    problems, snap = check_plan(plan)
    if problems:
        return dict(status="rejected", stage="plan", problems=problems)
    seen_ids = {}
    agg = dict(processed=0, split=0, atomic=0, infeasible=0, pending=0)
    final_pending = []
    infos = []
    for p in branch_paths:
        raw = Path(p).read_bytes()
        out = json.loads(raw)
        probs, info = verify_branch_output(out, plan)
        if probs:
            problems += ["%s: %s" % (p, x) for x in probs]
            continue
        bid = out["branch_id"]
        if bid in seen_ids:
            problems.append("branch %s supplied twice (%s, %s)"
                            % (bid, seen_ids[bid], p))
            continue
        seen_ids[bid] = p
        for k in agg:
            agg[k] += int(out.get("counts", {}).get(k, 0) or 0)
        for e in out.get("frontier", []):
            b = BX.decode(e["H"])
            if e.get("type") == "pending":
                final_pending.append(dict(box=e["H"], branch=bid,
                                          box_sha256=BX.box_hash(b)))
        infos.append(dict(path=str(p), sha256=BX.file_sha256(p), id=bid,
                          status=out.get("status"), counts=out.get("counts")))
    planned = {b["id"] for b in plan["branches"]}
    missing = sorted(planned - set(seen_ids))
    unknown = sorted(set(seen_ids) - planned)
    if missing:
        problems.append("missing branches: %s" % ",".join(missing))
    if unknown:
        problems.append("unknown branches: %s" % ",".join(unknown))
    # merged volume bookkeeping (exact)
    v_pending_old = sum(BX.volume(P) for P in snap["pendings"])
    v_new_pending = sum(mp["box"] and BX.volume(BX.decode(mp["box"]))
                        for mp in final_pending)
    dom = plan.get("domain")
    manifest = dict(schema=SCHEMA_MERGE, source=plan["source"],
                    plan=dict(path=str(plan_path), sha256=plan_sha256),
                    branches=infos, replaced_pending=len(snap["pendings"]),
                    new_frontier_pending=len(final_pending),
                    pending=final_pending,
                    counts=dict(source=snap["counts"], new=agg,
                                total_certified=int(snap["counts"].get(
                                    "certified", 0)) + agg["atomic"]),
                    volume=dict(old_pending=str(v_pending_old),
                                new_pending=str(v_new_pending)),
                    status=("certified-full-domain"
                            if not final_pending and not problems
                            else "partial"),
                    problems=problems)
    return manifest


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return
    cmd = sys.argv[1]
    if cmd == "plan":
        snap, outp = sys.argv[2], sys.argv[3]
        deep = 1
        if "--deep" in sys.argv:
            deep = int(sys.argv[sys.argv.index("--deep") + 1])
        plan = make_plan(snap, deep)
        text = json.dumps(plan, indent=1)
        Path(outp).write_text(text, encoding="utf8")
        print(json.dumps({"plan": outp, "sha256": BX.file_sha256(outp),
                          "branches": plan["branch_count"],
                          "pendings": plan["pending_count"]}, indent=1))
    elif cmd == "check":
        plan = json.loads(Path(sys.argv[3]).read_text())
        snap_arg = sys.argv[2]
        if not Path(snap_arg).is_file():
            alt = Path(sys.argv[3]).parent / snap_arg
            if alt.is_file():
                snap_arg = str(alt)
        problems, snap = check_plan(plan, snap_arg)
        print(json.dumps({"problems": problems,
                          "verdict": "OK" if not problems else "REJECTED",
                          "branches": plan["branch_count"],
                          "snapshot": plan["source"]}, indent=1))
    elif cmd == "merge":
        man = merge(sys.argv[2], sys.argv[3:])
        outp = "merge-manifest.json"
        Path(outp).write_text(json.dumps(man, indent=1), encoding="utf8")
        print(json.dumps({k: man[k] for k in
                          ("status", "counts", "volume", "problems")}, indent=1))
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
