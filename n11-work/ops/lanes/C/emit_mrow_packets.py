#!/usr/bin/env python3
"""Emit row-count-generic energy packets from an exact m-row certificate JSON.

The input format is intentionally small and self-contained::

  {
    "m": 10,
    "records": [
      {"id": 42, "pass": true,
       "beta": [16 exact rationals],
       "packets": [36 CosineLinePacket records],
       "row_from": [m integers], "row_to": [m integers],
       "lam": [m nonnegative exact rationals],
       "rmin": exact rational, "f0Lo": exact rational,
       "g": [9 exact rationals]}
    ]
  }

`m` may be omitted when every record has the same row count.  This script
recomputes the reduced-cost inequalities, lambda-bound term, and `lower` with
`Fraction` arithmetic from the frozen DBM.  Every emitted `Valid` is still
closed by `decide +kernel`; the Python audit is a guard against malformed or
obviously failing input, not a replacement for kernel credit.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
DBM = ROOT / "n11-work/lean/N11Formalization/DBMSourceTreeData.lean"
DEFAULT_OUT = ROOT / "n11-work/lean/N11Formalization"

T2 = Q(1899919265599193545242591, 5000000000000000000000000) ** 2
LQ = 2 * Q(449404532622434011541355675101, 1152921504606846976000000000000)
PI_LO = Q(314159265358979323846, 10**20)
PI_HI = Q(314159265358979323847, 10**20)
DQ = 9 * LQ - 2 * PI_LO
Dq = 9 * Q(2 * 1150475603510479590494077, 2951479051793528258560000) - 2 * PI_HI


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def as_q(value, where: str) -> Q:
    try:
        return Q(str(value))
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError(f"{where}: not an exact rational: {value!r}") from exc


def ql(value, where: str) -> str:
    q = as_q(value, where)
    return f"(({q.numerator} : ℚ)/{q.denominator})"


def vec(items: list[str]) -> str:
    return "![" + ",".join(items) + "]"


def line(p: dict, where: str) -> str:
    vals = [ql(p[k], f"{where}.{k}") for k in ("a", "b", "s", "c", "t", "e")]
    rule = p["rule"]
    if rule not in ("tangent", "decreasing"):
        raise ValueError(f"{where}.rule: unexpected rule {rule!r}")
    return "⟨" + ",".join(vals + [f"({int(p['shift'])} : ℤ)", "." + rule]) + "⟩"


def parse_db(text: str, node: int) -> list[list[int]]:
    match = re.search(
        rf"def node{node} : Node 5011 where\s*db := (.*?)\n\s*terminal :=",
        text,
        re.S,
    )
    if not match:
        raise ValueError(f"node {node} not found in frozen DBM source")
    nums = [int(x) for x in re.findall(r"-?\d+", match.group(1))]
    if len(nums) != 100:
        raise ValueError(f"node {node}: expected 100 DBM entries, got {len(nums)}")
    return [nums[10 * i:10 * i + 10] for i in range(10)]


def endpoint_lo(g: Q) -> Q:
    return g * Dq if 0 <= g else g * DQ


def row_a(i: int, j: int, q: int) -> int:
    return (1 if q < j else 0) - (1 if q < i else 0)


def audit_record(rec: dict, m: int, db_text: str) -> dict:
    rid = rec.get("id")
    if not isinstance(rid, int) or not 0 <= rid < 5011:
        raise ValueError(f"bad node id: {rid!r}")
    if rec.get("pass") is not True:
        raise ValueError(f"node {rid}: record is not certified as passing")
    if len(rec.get("beta", [])) != 16:
        raise ValueError(f"node {rid}: beta must have 16 entries")
    if len(rec.get("packets", [])) != 36:
        raise ValueError(f"node {rid}: packets must have 36 entries")
    for key in ("row_from", "row_to", "lam"):
        if len(rec.get(key, [])) != m:
            raise ValueError(f"node {rid}: {key} must have m={m} entries")
    if len(rec.get("g", [])) != 9:
        raise ValueError(f"node {rid}: g must have 9 entries")

    beta = [as_q(v, f"node {rid}.beta[{k}]") for k, v in enumerate(rec["beta"])]
    if any(v < 0 for v in beta) or sum(beta) != 1:
        raise ValueError(f"node {rid}: beta is not a probability vector")
    lam = [as_q(v, f"node {rid}.lam[{k}]") for k, v in enumerate(rec["lam"])]
    if any(v < 0 for v in lam):
        raise ValueError(f"node {rid}: negative dual multiplier")
    row_from = [int(v) for v in rec["row_from"]]
    row_to = [int(v) for v in rec["row_to"]]
    if any(not 0 <= v < 10 for v in row_from + row_to):
        raise ValueError(f"node {rid}: row endpoint outside Fin 10")

    db = parse_db(db_text, rid)
    rmin = as_q(rec["rmin"], f"node {rid}.rmin")
    g = [as_q(v, f"node {rid}.g[{q}]") for q, v in enumerate(rec["g"])]
    reduced = []
    for q in range(9):
        rhs = endpoint_lo(g[q]) + sum(
            lam[k] * row_a(row_from[k], row_to[k], q) for k in range(m)
        )
        if rmin > rhs:
            raise ValueError(f"node {rid}: reduced-cost inequality fails at q={q}")
        reduced.append(rhs)

    lam_b = sum(lam[k] * Q(db[row_from[k]][row_to[k]], 4096) for k in range(m))
    f0_lo = as_q(rec["f0Lo"], f"node {rid}.f0Lo")
    lower = f0_lo - lam_b + rmin
    if "lower" in rec and as_q(rec["lower"], f"node {rid}.lower") != lower:
        raise ValueError(f"node {rid}: recorded lower bound identity fails")
    gap = lower - T2
    if gap <= 0:
        raise ValueError(f"node {rid}: exact gap is not positive: {gap}")
    return {
        "id": rid,
        "rmin": rmin,
        "lower": lower,
        "gap": gap,
        "slack": min(rhs - rmin for rhs in reduced),
    }


def module_text(base: str, idx: int, subset: list[dict], m: int) -> str:
    ns = f"N11Formalization.{base}H{idx:02}"
    n = len(subset)
    text = f"""import N11Formalization.PaidBlock
import N11Formalization.PaidCellCertificateM
/-! {n} exact-rational {m}-row OWN-cell packets. `Valid` is paid only by
`decide +kernel`; the emitter's Fraction audit is not treated as proof. -/
set_option autoImplicit false
namespace {ns}
open Finset N11Formalization.PaidCellCertificateM
noncomputable section
set_option maxRecDepth 10000
abbrev M : ℕ := {m}
abbrev Case := Fin {n}
def nodeID : Case → Fin 5011 := {vec([str(r['id']) for r in subset])}
"""
    for i, r in enumerate(subset):
        values = [
            str(r["id"]),
            vec([ql(v, f"node {r['id']}.beta") for v in r["beta"]]),
            vec([line(p, f"node {r['id']}.packets[{k}]")
                 for k, p in enumerate(r["packets"])]),
            vec([str(v) for v in r["row_from"]]),
            vec([str(v) for v in r["row_to"]]),
            vec([ql(v, f"node {r['id']}.lam") for v in r["lam"]]),
            ql(r["rmin"], f"node {r['id']}.rmin"),
        ]
        text += f"def packet{i} : Packet M := ⟨" + ",".join(values) + "⟩\n"
        text += f"""theorem valid{i} : Valid packet{i} := by
  constructor <;> decide +kernel
"""
    text += f"def packet : Case → Packet M := {vec([f'packet{i}' for i in range(n)])}\n"
    text += "theorem all_valid (i : Case) : Valid (packet i) := by\n  fin_cases i\n"
    text += "".join(f"  · exact valid{i}\n" for i in range(n))
    text += """theorem node_binding (i : Case) : (packet i).nodeID = nodeID i := by
  fin_cases i <;> rfl
theorem terminal (i : Case) : (DBMSourceTree.data (nodeID i)).terminal = true := by
  simpa only [node_binding] using (all_valid i).terminal
theorem oracle_gt (i : Case) (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID i))
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2 <
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
  N11Formalization.PaidCellCertificateM.oracle_gt (packet i) (all_valid i) y hy0 hy1
    (by simpa only [node_binding] using hc)
theorem common_chart_radius (i : Case) (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID i))
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  N11Formalization.PaidCellCertificateM.common_chart_radius
    (packet i) (all_valid i) y hy0 hy1
    (by simpa only [node_binding] using hc) C Z r hf
def newIDs : Finset (Fin 5011) := univ.image nodeID
theorem new_count : newIDs.card = """ + str(n) + """ := by decide +kernel
theorem node_injective : Function.Injective nodeID := by
  unfold Function.Injective
  decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact terminal i
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact common_chart_radius i y hy0 hy1 hc C Z r hf
def block : N11Formalization.PaidBlock.Block := ⟨newIDs, new_terminal, new_radius⟩
end
"""
    text += f"end {ns}\n"
    for name in ("all_valid", "common_chart_radius", "new_count", "new_radius", "block"):
        text += f"#check @{ns}.{name}\n"
    for name in ("all_valid", "common_chart_radius", "new_radius"):
        text += f"#print axioms {ns}.{name}\n"
    return text


def load_records(path: Path) -> tuple[list[dict], int]:
    doc = json.loads(path.read_text(encoding="utf-8-sig"))
    if isinstance(doc, list):
        records, declared_m = doc, None
    elif isinstance(doc, dict):
        records = doc.get("records", doc.get("certificates"))
        declared_m = doc.get("m")
    else:
        raise ValueError("certificate JSON must be an object or list")
    if not isinstance(records, list) or not records:
        raise ValueError("certificate JSON contains no records")
    lengths = {len(r.get("lam", [])) for r in records}
    if len(lengths) != 1:
        raise ValueError(f"records do not share one row count: {sorted(lengths)}")
    inferred_m = lengths.pop()
    if declared_m is not None and int(declared_m) != inferred_m:
        raise ValueError(f"declared m={declared_m} but records use {inferred_m} rows")
    if inferred_m == 0:
        raise ValueError("m must be positive")
    ids = [r.get("id") for r in records]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate node ids")
    return records, inferred_m


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("certificates", type=Path)
    ap.add_argument("--base", default="PaidCellMResidual")
    ap.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    ap.add_argument("--group-size", type=int, default=21)
    ap.add_argument("--check-only", action="store_true")
    args = ap.parse_args()
    if args.group_size <= 0:
        raise ValueError("group-size must be positive")

    records, m = load_records(args.certificates)
    db_text = DBM.read_text()
    audits = [audit_record(r, m, db_text) for r in records]
    records.sort(key=lambda r: r["id"])
    audits.sort(key=lambda r: r["id"])
    summary = {
        "scope": "exact-rational preflight; kernel Valid proof is separate",
        "input": str(args.certificates),
        "input_sha256": sha(args.certificates),
        "dbm_sha256": sha(DBM),
        "m": m,
        "records": len(records),
        "min_exact_gap": str(min(a["gap"] for a in audits)),
        "min_reduced_slack": str(min(a["slack"] for a in audits)),
        "modules": [],
    }
    if args.check_only:
        print(json.dumps(summary, indent=2))
        return 0

    args.out_dir.mkdir(parents=True, exist_ok=True)
    groups = [records[i:i + args.group_size]
              for i in range(0, len(records), args.group_size)]
    for idx, subset in enumerate(groups, 1):
        path = args.out_dir / f"{args.base}H{idx:02}.lean"
        data = module_text(args.base, idx, subset, m).encode("utf-8")
        if path.exists():
            if path.read_bytes() != data:
                raise FileExistsError(f"existing module differs: {path}")
            reused = True
        else:
            path.write_bytes(data)
            reused = False
        summary["modules"].append({
            "path": str(path), "records": len(subset),
            "sha256": sha(path), "reused": reused,
        })
    manifest = args.out_dir / f"{args.base}-manifest.json"
    manifest.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "modules"}, indent=2))
    for item in summary["modules"]:
        print(item["records"], item["sha256"], item["path"])
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:  # concise CLI failure without a traceback wall
        print(f"emit_mrow_packets: ERROR: {exc}", file=sys.stderr)
        sys.exit(1)
