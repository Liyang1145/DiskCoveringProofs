"""Verify the FULL telescope shape independently, end to end, from source.

Chain claim: for S = 12..36, module C450Source<S>Segment supplies
  source<S-1>_remaining_of_remaining : <own>.obl -> C450Source<S-1>Segment.obl
and its body consumes its OWN source<S>_paid.

If that holds for every S, then composing S=36 down to S=12 yields
  Source36.obl -> Source35.obl -> ... -> Source12.obl -> Source11.obl = h450
with Source36.obl vacuous, so h450 is dischargeable from the 24 paid proofs.
"""
import re
from pathlib import Path

base = Path(r"E:\ai4math2\research-2026\n11-formalization\lean\N11Formalization")

print("S -> name / conclusion / own paid / pred import / body uses own paid")
print("-" * 78)
viol = []
for S in range(12, 37):
    p = base / f"C450Source{S}Segment.lean"
    if not p.exists():
        viol.append((S, "MISSING FILE"))
        print(f"  {S:2d}  MISSING FILE")
        continue
    t = p.read_text(encoding="utf-8")
    name = f"theorem source{S-1}_remaining_of_remaining"
    conc = f"C450Source{S-1}Segment.RemainingSourceObligation"
    has_name = name in t
    has_conc = conc in t
    has_paid = f"source{S}_paid" in t
    has_imp = f"import N11Formalization.C450Source{S-1}Segment" in t
    # does the BODY of the step consume its own paid proof?
    m = re.search(
        rf"theorem source{S-1}_remaining_of_remaining.*?(?=\ntheorem |\nend )", t, re.S)
    body_paid = bool(m) and (f"source{S}_paid" in m.group(0))
    ok = has_name and has_conc and has_paid and has_imp and body_paid
    if not ok:
        viol.append((S, dict(name=has_name, conc=has_conc, paid=has_paid,
                             imp=has_imp, body=body_paid)))
    print(f"  {S:2d}  {int(has_name)} / {int(has_conc)} / {int(has_paid)} / "
          f"{int(has_imp)} / {int(body_paid)}   {'OK' if ok else 'BAD'}")

print("-" * 78)
print(f"modules checked 12..36 : {36-12+1}")
print(f"violations             : {len(viol)}")
for v in viol:
    print("   ", v)

# the two terminal facts
print("\nterminal facts:")
t36 = (base / "C450Source36Segment.lean").read_text(encoding="utf-8")
print(f"  Source36 drop 36        : {'c450Segs.drop 36' in t36}")
print(f"  Source36 remaining = 0   : {'remaining_count : remainingSegs.length = 0' in t36}")
print(f"  Source36 has own paid    : {'source36_paid' in t36}")
t11 = (base / "C450Source11Segment.lean").read_text(encoding="utf-8")
print(f"  Source11 defines h450    : {'def RemainingSourceObligation' in t11}")
print(f"  Source11 remaining = 25  : {'remaining_count : remainingSegs.length = 25' in t11}")

# arithmetic consistency of the whole chain
print("\narithmetic floor check (drop d must give 36-d entries):")
ok = True
for S in range(11, 37):
    t = (base / f"C450Source{S}Segment.lean").read_text(encoding="utf-8")
    m = re.search(r"c450Segs\.drop (\d+)", t)
    m2 = re.search(r"remaining_count\s*:\s*remainingSegs\.length = (\d+)", t)
    if not m or not m2:
        print(f"  S={S}: could not parse")
        ok = False
        continue
    d, c = int(m.group(1)), int(m2.group(1))
    if d + c != 36:
        print(f"  S={S}: drop {d} + count {c} = {d+c} != 36  BAD")
        ok = False
    else:
        print(f"  S={S:2d}: drop {d:2d} + count {c:2d} = 36  ok")
print(f"\narithmetic consistent: {ok}")
