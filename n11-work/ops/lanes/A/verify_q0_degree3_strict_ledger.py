#!/usr/bin/env python3
"""Exact-rational audit of every coarse bound in `SevenClassQ0Deg3StrictTotal`.

This checks the emitted Lean constants against the inequalities named in
`canonicalLedger_lt_piLo`.  It is source/arithmetic evidence, not a kernel proof.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization/SevenClassQ0Deg3UpperTables.lean"
STRICT = ROOT / "n11-work/lean/N11Formalization/SevenClassQ0Deg3StrictTotal.lean"
SCALE = 10**6
PI_LO = Fraction(314159265358979323846, 10**20)
PI_HI = Fraction(314159265358979323847, 10**20)


def lean_array(source: str, name: str) -> list[str]:
    start = source.index(f"def {name} ")
    start = source.index(":= ![", start) + len(":= ![")
    depth = 1
    end = start
    while depth:
        depth += source[end] in "[("
        depth -= source[end] in "])"
        end += 1
    body = source[start:end - 1]
    fields: list[str] = []
    field_start = 0
    depth = 0
    for index, char in enumerate(body + ","):
        if char in "[(":
            depth += 1
        elif char in "])":
            depth -= 1
        elif char == "," and depth == 0:
            fields.append(body[field_start:index].strip())
            field_start = index + 1
    return fields


def rational(text: str) -> Fraction:
    text = text.strip().replace(" ", "").split(":", 1)[0]
    text = text.removeprefix("(").removesuffix(")")
    return Fraction(text)


def ceil_scaled(value: Fraction) -> Fraction:
    return Fraction((value.numerator * SCALE + value.denominator - 1) // value.denominator, SCALE)


def main() -> None:
    source = LEAN.read_text()
    strict_source = STRICT.read_text()
    mu = [rational(x) for x in lean_array(source, "mu")]
    edge_max = [rational(x) for x in lean_array(source, "edgeMaxAt")]
    sector_max = [rational(x) for x in lean_array(source, "sectorMax")]
    lam = rational(source.split("def lam : ℚ := ", 1)[1].splitlines()[0])
    edge_bound = [rational(x) for x in lean_array(strict_source, "edgeBoundAt")]
    sector_bound = [rational(x) for x in lean_array(strict_source, "sectorBoundAt")]
    pair_bounds = [rational(x) for x in lean_array(strict_source, "edgePairAbsBoundAt")]
    edges = []
    for field in lean_array(source, "tableEdges"):
        text = field.strip().lstrip("(")
        text = text[:text.index("}")].replace("{", "")
        edges.append(tuple(int(x) for x in text.split(",")))

    assert len(mu) == 11 and len(edge_max) == 21
    assert len(sector_max) == 9 and len(edges) == 21
    assert all(len(edge) == 2 for edge in edges)

    total_coeff = 2 * (sum(mu) - lam)
    assert edge_bound == [ceil_scaled(x) for x in edge_max]
    assert sector_bound == [ceil_scaled(x) for x in sector_max]
    edge_pair_abs = [abs(sum(mu[j] for j in edge)) for edge in edges]
    edge_increment = sum((Fraction(19, 50) ** 2 + value) * PI_HI / 2048
                         for value in pair_bounds)
    sector_increment = sum((1 + lam + abs(mu[(i + 1) % 9])) * PI_HI / 2048
                           for i in range(9))

    checks = {
        "totalCoeff <= -319/1000": total_coeff <= Fraction(-319, 1000),
        "lam <= 1/5": lam <= Fraction(1, 5),
        "all |mu(nextSite i)| <= 1/20": all(abs(mu[(i + 1) % 9]) <= Fraction(1, 20)
                                              for i in range(9)),
        "all |edge sum| <= declared caps": all(x <= y for x, y in zip(edge_pair_abs, pair_bounds)),
        "edgeMaxAt <= six-decimal caps": all(x <= y for x, y in zip(edge_max, edge_bound)),
        "sectorMax <= six-decimal caps": all(x <= y for x, y in zip(sector_max, sector_bound)),
        "edge cap sum <= 2134315/1e6": sum(edge_bound) <= Fraction(2_134_315, SCALE),
        "sector cap sum <= 1977695/1e6": sum(sector_bound) <= Fraction(1_977_695, SCALE),
        "edge increments <= 8/1000": edge_increment <= Fraction(8, 1000),
        "sector increments <= 18/1000": sector_increment <= Fraction(18, 1000),
        "totalCoeff*piLo <= -1": total_coeff * PI_LO <= -1,
    }
    failed = [name for name, passed in checks.items() if not passed]
    if failed:
        raise SystemExit("FAIL\n" + "\n".join(failed))

    ledger_upper = (Fraction(-1) + Fraction(2_134_315, SCALE) +
                    edge_increment + Fraction(1_977_695, SCALE) + sector_increment)
    assert ledger_upper < PI_LO
    print(f"PASS: 11/11 named coarse bounds; totalCoeff={float(total_coeff):.15f}")
    print(f"PASS: exact ledger upper={float(ledger_upper):.15f}, piLo slack={float(PI_LO-ledger_upper):.15f}")
    print("Scope: exact rational source audit; no Lean kernel verdict.")


if __name__ == "__main__":
    main()
