"""Formal sparse-polynomial identities underlying full-cover cone triangles."""
from pathlib import Path
import argparse
import json
import quadratic_cover_sos as P
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def weighted(values, weights):
    return P.add(*(P.mul(value, weight) for value, weight in zip(values, weights, strict=True)))


def distance(first, last):
    return P.square(P.add(first, P.scaled(last, -1)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    lam, a, b, p, s = [P.variable(i) for i in range(5)]
    weights = [lam, P.add(P.constant(1), P.scaled(lam, -1))]
    y = weighted([a, b], weights)
    x = P.add(P.mul(P.add(P.constant(1), P.scaled(s, -1)), p), P.mul(s, y))
    atx = weighted([distance(x, a), distance(x, b)], weights)
    atp = weighted([distance(p, a), distance(p, b)], weights)
    difference = P.add(atx, P.scaled(atp, -1))
    exact_factor = P.mul(P.add(P.square(s), P.scaled(s, -2)), distance(p, y))
    assert difference == exact_factor
    w1, w2, a, b, c, p = [P.variable(i) for i in range(6)]
    w3 = P.add(P.constant(1), P.scaled(w1, -1), P.scaled(w2, -1))
    weights = [w1, w2, w3]
    centers = [a, b, c]
    x = weighted(centers, weights)
    atx = weighted([distance(x, center) for center in centers], weights)
    atp = weighted([distance(p, center) for center in centers], weights)
    assert P.add(atx, distance(x, p)) == atp
    # Exact identities are coordinatewise; summing them proves the planar
    # statements for all real coordinates, not only the sampled candidates.
    report = {"verified": True, "two_center_cone_identity_all_coefficients_checked": True,
              "three_center_variance_identity_all_coefficients_checked": True,
              "two_center_difference_factor": "s*(s-2)*|p-y|^2",
              "nonpositive_for_s_in_closed_unit_interval": True,
              "inequality_requires_nonnegative_normalized_center_weights": True,
              "no_extra_disk_at_the_witness_used": True,
              "candidate_geometry_sampling_not_used": True,
              "source_sha256": sha(Path(__file__)),
              "polynomial_kernel_sha256": sha(ROOT / "quadratic_cover_sos.py"),
              "written_lemma_sha256": sha(ROOT / "COMMON-WITNESS-CONING-LEMMA.md"),
              "scope": "complete formal polynomial identities plus elementary sign argument"}
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Common-witness cone algebra PASS: full coefficient identities, no extra disk at anchor", flush=True)


if __name__ == "__main__":
    main()
