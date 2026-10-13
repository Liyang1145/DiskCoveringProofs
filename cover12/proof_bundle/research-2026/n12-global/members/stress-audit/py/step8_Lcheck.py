"""stress-audit step 8: L = 2 asin(U) bracket - whose value is right?

mpmath dps=100: compute 2 asin(U), sin(L/2) for both endpoints of the lead's
recorded bracket, and test the lead's own trig() enclosure on those endpoints.
"""
from fractions import Fraction as F
from pathlib import Path
import json, sys
sys.set_int_max_str_digits(10**6)
import mpmath as mp

mp.mp.dps = 100
N12 = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\n12-global")
cert = json.loads((N12 / 'evidence/network-certified-234.json').read_text(encoding='utf-8'))
U = F('0.361102963744508672616920293904')
print("full constant_intervals:")
print(json.dumps(cert['constant_intervals'], indent=1))
Lb = [F(s) for s in cert['constant_intervals']['L']]
Db = [F(s) for s in cert['constant_intervals']['D']]
pi_b = [F(s) for s in cert['constant_intervals']['pi']]
print("\nL interval : [", mp.nstr(mp.mpf(Lb[0].numerator)/Lb[0].denominator, 45), ",",
      mp.nstr(mp.mpf(Lb[1].numerator)/Lb[1].denominator, 45), "]")
print("D interval : [", mp.nstr(mp.mpf(Db[0].numerator)/Db[0].denominator, 25), ",",
      mp.nstr(mp.mpf(Db[1].numerator)/Db[1].denominator, 25), "]")
print("pi interval: [", mp.nstr(mp.mpf(pi_b[0].numerator)/pi_b[0].denominator, 35), ",",
      mp.nstr(mp.mpf(pi_b[1].numerator)/pi_b[1].denominator, 35), "]")

Um = mp.mpf(U.numerator) / U.denominator
Lmp = 2 * mp.asin(Um)
print("\nmy 2 asin(U)      = ", mp.nstr(Lmp, 55))
print("their L_lo        = ", mp.nstr(mp.mpf(Lb[0].numerator) / Lb[0].denominator, 55))
print("their L_hi        = ", mp.nstr(mp.mpf(Lb[1].numerator) / Lb[1].denominator, 55))
print("Lmp - Lhi         = ", mp.nstr(Lmp - mp.mpf(Lb[1].numerator) / Lb[1].denominator, 8))
print("Lmp - Llo         = ", mp.nstr(Lmp - mp.mpf(Lb[0].numerator) / Lb[0].denominator, 8))

print("\nsin(L/2) tests (true L must satisfy sin(L/2)=U exactly):")
for nm, v in (("my L/2", Lmp / 2),
              ("their lo/2", mp.mpf(Lb[0].numerator) / Lb[0].denominator / 2),
              ("their hi/2", mp.mpf(Lb[1].numerator) / Lb[1].denominator / 2)):
    print(f"  sin({nm}) - U = {mp.nstr(mp.sin(v) - Um, 8)}")
print(f"  U = {mp.nstr(Um, 50)}")

# what U would their L correspond to?
print("\nimplied U from their endpoints: sin(lo/2) =", mp.nstr(mp.sin(mp.mpf(Lb[0].numerator)/Lb[0].denominator/2), 45))
print("implied U from their endpoints: sin(hi/2) =", mp.nstr(mp.sin(mp.mpf(Lb[1].numerator)/Lb[1].denominator/2), 45))
print("D consistency: 9*Llo-2*pi_hi, 9*Lhi-2*pi_lo =",
      mp.nstr(9 * mp.mpf(Lb[0].numerator) / Lb[0].denominator - 2 * mp.mpf(pi_b[1].numerator) / pi_b[1].denominator, 25),
      mp.nstr(9 * mp.mpf(Lb[1].numerator) / Lb[1].denominator - 2 * mp.mpf(pi_b[0].numerator) / pi_b[0].denominator, 25))

print("\n=== lead trig() enclosure test ===")
sys.path.insert(0, str(N12 / 'lead'))
try:
    import network_interval_certificate as NC
    for nm, x in (("their lo/2", Lb[0] / 2), ("their hi/2", Lb[1] / 2), ("my L/2", F(mp.nstr(Lmp / 2, 90)).limit_denominator(10**90) if False else F(0))):
        if x == 0:
            continue
        t = NC.trig(x, 'sin')
        tl = mp.mpf(t.lo.numerator) / t.lo.denominator
        th = mp.mpf(t.hi.numerator) / t.hi.denominator
        true = mp.sin(mp.mpf(x.numerator) / x.denominator)
        print(f"  {nm}: enclosure [{mp.nstr(tl, 20)}, {mp.nstr(th, 20)}] width {mp.nstr(th - tl, 6)}")
        print(f"      true sin = {mp.nstr(true, 30)}   contained: {tl <= true <= th}"
              f"   enclosure.hi < U: {float(th) < float(Um)}")
except Exception as exc:
    print("  import/exec failed:", repr(exc))
