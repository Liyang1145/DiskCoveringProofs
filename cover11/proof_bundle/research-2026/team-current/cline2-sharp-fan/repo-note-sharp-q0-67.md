# repo-note-sharp-q0-67.md — RETRACTED

This note is RETRACTED IN FULL by its author after Lead review.

Reasons (see STATUS.md ERRATA E1–E6 in this same directory):

- Its Section 2 ("Finite criterion": covering radius attained in {switches} u {tips})
  rests on a false concavity argument. The correct identity is
      min_k |x - c_k|^2 = |x|^2 + min_k (|c_k|^2 - 2 x.c_k),
  which is NOT concave (|x|^2 is convex; with a centre at the origin the objective is
  |x|^2). The candidate set also omits the antipodal boundary points and the hub-hub
  Voronoi vertices. Numeric falsification: out/p21_criterion_stress.txt (400 random
  configurations, worst gap 8.02e-01) and out/p22_domain_stress.txt (120 configurations
  whose rings cover bd D, worst gap 1.88e-01).
- Section 4/5 use that criterion plus a mislabelled run-length pair ((4,3) is wrong;
  the correct run lengths are (4,5)) and a mislabelled saturation statement at R=0.38
  (the candidate is unsaturated: covering radius 0.3799838531... < 0.38, so its rings
  are not pairwise separated by 2R). "|c| + R >= 1" means the ring disk REACHES bd D,
  not that the ring is interior.
- A switch is the nearest-site bisector intersection with bd D, not universally the
  intersection of the two radius-R circles.

Nothing in this file may be cited as a reduction, a certificate, or as support for the
sharp value. The only surviving material of this round is the numeric output listed in
STATUS.md section "WHAT REMAINS" (N1–N6).
