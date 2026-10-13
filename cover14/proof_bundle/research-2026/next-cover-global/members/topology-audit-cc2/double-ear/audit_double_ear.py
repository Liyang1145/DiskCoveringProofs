"""Independent audit of lead/Q11-DOUBLE-EAR-EXCLUSION.md (scope: members/topology-audit-cc2/double-ear).

Check A (exact rational constant): 2*pi > 4 asin(2r) + 10 asin(r) at r=U, decided in Fractions.
   asin(x) = sum_n C(2n,n) x^(2n+1)/(4^n (2n+1)); all terms positive, so the N-term partial sum
   is a LOWER bound and adding the explicit tail x^(2N+1)/(1-x^2) (using C(2n,n)/4^n <= 1) gives
   an UPPER bound.  pi via Machin 16 atan(1/5) - 4 atan(1/239) with alternating two-sided bounds.
   Control: at r=1/3 the same certificate must FAIL (margin negative).

Check B (catalogue): re-derive the pruning of lead/q11-pocket-catalogue.json:
   an ALL-RING face is a face-triple whose three vertices are all < 11; as a triangle of the
   complex its vertices are pairwise adjacent in the 11-cycle, i.e. it is a consecutive triple
   {i-1,i,i+1}.  Correct wrap-aware test:
       any(set(f) == {(i-1)%11, i, (i+1)%11} for i in range(11))
   (an earlier sorted-gap test wrongly rejected the wrap-around ears {10,0,1},{9,10,0},...).
   A pair of such faces is pruned iff their vertex sets are disjoint.  Compare the retained set
   and the by-chord histogram with lead/q11-double-ear-pruning.json.
"""
import json
import sys
sys.set_int_max_str_digits(200000)
from fractions import Fraction as Q
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAD = HERE.parents[2] / "lead"
U = Q(33173203427623414, 10 ** 17)
N = 11


def asin_bounds(x, Nterms=40):
    lo = sum((Q(comb(2 * n, n), 4 ** n * (2 * n + 1)) * x ** (2 * n + 1)
              for n in range(Nterms)), Q(0))
    return lo, lo + x ** (2 * Nterms + 1) / (1 - x * x)


def atan_bounds(x, Nterms=30):
    s = sum((Q((-1) ** n) * x ** (2 * n + 1) / (2 * n + 1) for n in range(Nterms)), Q(0))
    nxt = Q((-1) ** Nterms) * x ** (2 * Nterms + 1) / (2 * Nterms + 1)
    return min(s, s + nxt), max(s, s + nxt)


def certificate(r=U):
    a_lo, a_hi = asin_bounds(r)
    b_lo, b_hi = asin_bounds(2 * r)
    rhs_lo = 10 * a_lo + 4 * b_lo
    rhs_hi = 10 * a_hi + 4 * b_hi
    u = atan_bounds(Q(1, 5))
    v = atan_bounds(Q(1, 239))
    pi_lo = 16 * u[0] - 4 * v[1]
    pi_hi = 16 * u[1] - 4 * v[0]
    return dict(rhs_upper=float(rhs_hi), rhs_lower=float(rhs_lo),
                two_pi_lower=float(2 * pi_lo), two_pi_upper=float(2 * pi_hi),
                margin_lower=float(2 * pi_lo - rhs_hi),
                margin_upper=float(2 * pi_hi - rhs_lo),
                decision_positive=bool(2 * pi_lo - rhs_hi > 0))


def is_ear(v):
    """v: iterable of three ring labels; true iff it is a consecutive triple {i-1,i,i+1}."""
    s = set(v)
    return len(s) == 3 and any(s == {(i - 1) % N, i, (i + 1) % N} for i in range(N))


def scan_catalogue():
    D = json.loads((LEAD / "q11-pocket-catalogue.json").read_text(encoding="utf-8"))
    kept, removed, hist = [], [], {}
    total_faces = failing = 0
    for idx, e in enumerate(D["entries"]):
        ears = [frozenset(f) for f in e["faces"] if max(f) < N]
        for f in ears:
            total_faces += 1
            if not is_ear(f):
                failing += 1
        pair = None
        for i in range(len(ears)):
            for j in range(i + 1, len(ears)):
                if not (ears[i] & ears[j]):
                    pair = (sorted(ears[i]), sorted(ears[j]))
                    break
            if pair:
                break
        key = str(len(e["chord_middle_representative"]))
        hist.setdefault(key, [0, 0])
        if pair:
            hist[key][1] += 1
            removed.append(idx)
        else:
            hist[key][0] += 1
            kept.append(idx)
    return dict(n=len(D["entries"]), kept=kept, removed=removed, hist=hist,
                all_ring_faces=total_faces, failing_consecutive_test=failing)


def main():
    res = {"A_certificate_U": certificate(U),
           "A_control_r_1_3": certificate(Q(1, 3)),
           "A_lead_display": "3.8938865969777676e-05"}
    sc = scan_catalogue()
    res["B_catalogue"] = {k: v for k, v in sc.items() if k not in ("kept", "removed")}
    res["B_catalogue"]["kept_count"] = len(sc["kept"])
    res["B_catalogue"]["removed_count"] = len(sc["removed"])
    try:
        P = json.loads((LEAD / "q11-double-ear-pruning.json").read_text(encoding="utf-8"))
        res["B_vs_lead"] = dict(
            lead_before=P["before"], lead_retained=P["retained_count"],
            lead_removed=P["removed_count"],
            lead_hist={k: list(v) for k, v in
                       sorted(P["by_chord_count_retained_removed"].items())},
            my_hist={k: list(v) for k, v in sorted(sc["hist"].items())},
            kept_sets_equal=(sorted(P["retained_indices"]) == sorted(sc["kept"])),
            removed_sets_equal=(sorted(w["index"] for w in P["removed_witnesses"])
                                == sorted(sc["removed"])),
        )
    except Exception as ex:
        res["B_vs_lead"] = {"error": str(ex)}
    (HERE / "double-ear-audit.json").write_text(json.dumps(res, indent=1), encoding="utf-8")
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
