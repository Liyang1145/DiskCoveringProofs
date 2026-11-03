#!/usr/bin/env python3
"""Emit `EnergyRefineN3490Repair.lean` / `EnergyRefineN3825Repair.lean`.

CI run 41600479881 built `EnergyRefineN3490.lean:188:0` and
`EnergyRefineN3825.lean:78:0` to a deterministic `whnf` timeout at the default
200000 heartbeats.  Both failures are the same monolithic, backtracking
`pk_ok` block

    fin_cases l <;> first | exact absurd hl (by decide +kernel) | exact ⟨validN, rfl, rfl⟩ ...

which re-elaborates the `by decide +kernel` negation for *every* branch, including
the ~35 true-terminal branches.  `EnergyRefineN0039Repair` (CI exit 0) shows the
fix: enumerate the `Fin K` cases and emit, per index, exactly one branch.

This emitter preserves the archive bytes (it only rewrites the `pk_ok` block),
reuses the same namespace so the module is a drop-in replacement, and self-checks
that every true-terminal index has a `validN` theorem.
"""
import hashlib
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[1] / "lean/N11Formalization"

STEMS = ["EnergyRefineN3490", "EnergyRefineN3825"]

FORBIDDEN = ["sorry", "admit", "axiom", "native_decide", "ofReduceBool",
             "implemented_by", "maxHeartbeats"]

PK_OK_HEADER = (
    "theorem pk_ok : \u2200 l, (sub l).terminal = true \u2192 MValid (pk l) \u2227 "
    "(pk l).D = (sub l).db \u2227 (pk l).S = 1048576 := by"
)


def parse(stem):
    src = (LEAN / f"{stem}.lean").read_text(encoding="utf-8")
    K = int(re.search(r"^abbrev K := (\d+)$", src, re.M).group(1))
    sub = re.search(r"^def sub : Fin K \u2192 Node K := !\[(.*)\]$", src, re.M).group(1)
    sub = [s.strip() for s in sub.split(",")]
    pk = re.search(r"^def pk : Fin K \u2192 MPacket := !\[(.*)\]$", src, re.M).group(1)
    pk = [s.strip() for s in pk.split(",")]
    assert len(sub) == K and len(pk) == K, (stem, K, len(sub), len(pk))
    terms = {}
    for m in re.finditer(r"^def (node\d+) : Node K := (.*)$", src, re.M):
        t = re.search(r"\]\],(true|false),", m.group(2))
        assert t, m.group(1)
        terms[m.group(1)] = t.group(1) == "true"
    valids = set(re.findall(r"^theorem (valid\d+) :", src, re.M))
    return src, K, sub, pk, terms, valids


def build_block(K, sub, pk, terms, valids):
    lines = [PK_OK_HEADER, "  intro l hl", "  fin_cases l"]
    true_idx = []
    for i in range(K):
        if terms[sub[i]]:
            v = "valid" + pk[i][2:]
            if v not in valids:
                raise SystemExit(f"index {i}: terminal=true but no {v} theorem")
            lines.append(f"  \u00b7 exact \u27e8{v}, rfl, rfl\u27e9")
            true_idx.append(i)
        else:
            lines.append("  \u00b7 exact False.elim (Bool.false_ne_true hl)")
    return "\n".join(lines) + "\n", true_idx


def emit(stem):
    src, K, sub, pk, terms, valids = parse(stem)
    start = src.index(PK_OK_HEADER)
    end = src.index("theorem terminal :", start)
    old_block = src[start:end]
    if "first |" not in old_block:
        raise SystemExit(f"{stem}: expected a backtracking `first |` pk_ok block")
    new_block, true_idx = build_block(K, sub, pk, terms, valids)
    out = src[:start] + new_block + src[end:]
    for tok in FORBIDDEN:
        if tok in out:
            raise SystemExit(f"{stem}: forbidden token {tok!r} in output")
    if "first |" in new_block:
        raise SystemExit("emitter still produced backtracking")
    out_path = LEAN / f"{stem}Repair.lean"
    out_path.write_text(out, encoding="utf-8")
    print(f"{out_path.name}: K={K} leaves={len(true_idx)} "
          f"cases={new_block.count(chr(10) + '  \u00b7')} "
          f"sha256={hashlib.sha256(out.encode()).hexdigest()}")
    print(f"  source sha256={hashlib.sha256(src.encode()).hexdigest()}")
    return true_idx


def main():
    for stem in STEMS:
        emit(stem)


if __name__ == "__main__":
    sys.exit(main())
