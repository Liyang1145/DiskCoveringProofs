"""Exact constants for the written actual-cover normalization/hub lemma."""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
import argparse
import json
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def sqrt_hi(value):
    scale = 10**80
    root = isqrt(value.numerator*scale*scale//value.denominator)
    if F(root, scale)**2 < value:
        root += 1
    result = F(root, scale)
    assert result**2 >= value
    return result


def constants(n, B, centers, faces):
    path = ROOT.parent / f"evidence/core-reduction/constants/n{n}.json"
    data = json.loads(path.read_text())
    assert data["verified"] and data["N"] == n and 3 <= B <= centers <= n
    assert any(row[0] == B for row in data["families"])
    U = F(data["radius_upper"])
    I = data["minimum_interior_cells"]
    assert I in (7, 8) and data["maximum_boundary_cells"] == n-I
    Q = F(2771, 5000) if I == 7 else F(1, 2)
    assert U/(1-2*U) < Q and U < F(1, 3)
    boundary = sqrt_hi(1-U*U)
    hub = 1-Q+2*Q*U
    assert 0 < hub < 1-U < boundary < 1
    inner = hub if B == n-I else F(1)
    radii = [F(1)]*(B-1)+[boundary]*B+[inner]*(centers-B)+[F(1)]*faces
    assert len(radii) == B+centers+faces-1
    return data, radii, {"N": n, "B": B, "radius_upper": str(U),
                         "boundary_radius_bound": str(boundary),
                         "interior_radius_bound": str(inner),
                         "essential_hub_branch": B == n-I, "auxiliary_Q": str(Q),
                         "hub_gap_from_U_boundary": str(1-U-hub),
                         "base_constants_sha256": sha(path),
                         "scope": "actual covers after U-footprint inward normalization, not unrestricted rod realizations"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    reports = []
    for n in (21, 22, 23, 24, 25):
        source = ROOT.parent / f"evidence/core-reduction/constants/n{n}.json"
        for B, I in json.loads(source.read_text())["families"]:
            data, radii, report = constants(n, B, n, 2*n-B-2)
            report["radii"] = list(map(str, radii))
            reports.append(report)
    result = {"verified_constants": True, "bounds": reports,
              "written_lemma_sha256": sha(ROOT / "ACTUAL-NORM-BOUNDS.md"),
              "source_sha256": sha(Path(__file__)),
              "new_family_exclusion_proved": False, "global_optimality_proved": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2), encoding="utf8")
    print("Actual-cover node norm bounds exact constants PASS", len(reports), flush=True)


if __name__ == "__main__":
    main()
