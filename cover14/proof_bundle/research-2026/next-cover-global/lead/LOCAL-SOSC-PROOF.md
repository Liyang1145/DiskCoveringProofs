# Strict local optimality among arbitrary 14 centers, modulo rotation

**Proof level:** analytic proof with integer-directed interval controls; independent non-box interface audit accepted (members/root-cc2/local-sosc-audit/AUDIT.md). **Not a global optimum theorem.** The configuration is the exact root construction of C1167.

## 1. A local necessary optimization problem

Let C∈R^28 list the 14 centers and let R denote the squared covering radius. Use 24 smooth functions f_k(C): ten squared distances at specified boundary nearest-site switches, and fourteen squared circumradii at the tight interior Voronoi vertices. Every sufficiently nearby cover must satisfy f_k(C)≤R.

This necessity is checked geometrically, not assumed from a fixed diagram: at the candidate, each selected boundary switch is transverse and strictly farther from every nonincident site; every selected interior circumcenter lies strictly inside D, its triangle is noncollinear, and every other site is strictly farther. These strict properties persist in a neighborhood. `local_sosc_certificate.py` explicitly certifies all these inequalities over C1167's root box. Exact active equalities f_k(C*)=r*² follow from `ROOT-ATTAINMENT.md`, not from intervals containing zero. The same script verifies the boundary branch signs against the exact symbolic anchors.

The boundary functions are the appropriate unit-circle/bisector intersection branches; the interior functions are rational circumradius-squared functions. All are C² locally. Other covering constraints may safely be omitted because we prove a local lower bound for this necessary relaxation.

Use the rotation gauge y(X+)=0. In the script's ordering X+ is site9, so this is coordinate19. Locally x(X+)>0, and every nearby configuration has a unique small rotation into this gauge.

## 2. Exact KKT stationarity, without a numerical rank assumption

The following five D2-orbits receive one common multiplier per orbit:

| Orbit | Contact type | Multiplicity | Script indices |
|---|---|---:|---|
| B_XA | X/A boundary switch | 4 | 0,4,5,9 |
| B_AC | A/C boundary switch | 4 | 1,3,6,8 |
| B_CC | two reflected C sites, y-axis switch | 2 | 2,7 |
| T_ACT | A,C,T circumcircle | 4 | 10,13,16,19 |
| T_AZT | A,Z,T circumcircle | 4 | 12,15,18,21 |

The six other tight triangles receive multiplier zero. The code independently checks these orbits using exact signed-coordinate reflection permutations of the sites and incidence sets.

An orbit-summed gradient is D2-invariant. Its restriction to the fixed tangent space with coordinates (a,b,c,d,s,z,t) determines the entire 28-coordinate invariant gradient: the Euclidean inner product identifies the invariant tangent and cotangent spaces. Thus no nonsymmetric stationarity equations are omitted by examining these seven directions.

### Two columns vanish analytically

Only B_XA among the five positive orbits depends on s. At its switch p=(s,±r), X=(s,0), so (p−X)·(1,0)=0. Holding A fixed and varying X radially, differentiating the unit-circle and pairwise equal-distance equations gives p'=0, since their intersection is transverse. Hence the squared-distance derivative with respect to s is exactly zero.

Only T_AZT among the five positive orbits depends on z. Its circumcenter is w=(±z,±r), and w−Z is vertical. If β_i are the circumcenter's barycentric coordinates, differentiation of the three equal-distance equations gives

    d(circumradius²) = −2 Σ_i β_i (w−c_i)·dc_i.

Indeed Σβ_i=1 and Σβ_i(w−c_i)=0 eliminate dw. Horizontal variation of Z therefore has derivative zero. Noncollinearity suffices for this identity; barycentric positivity is not required.

Consequently the five orbit-gradient rows act on only five effective coordinates (a,b,c,d,t).

### Their rank is at most four, exactly

C1173 supplies the implicit contact curve z↦(c(z),r(z)) solving the original F=G=0, with r'(z*)=0. The radical construction along this curve satisfies all five positive contact-orbit equations f_k(C(z))=r(z)². Differentiating at z* annihilates their gradients. The effective tangent is nonzero because

    a'=(s'+1)/2=1/2,

where s'=0 follows from r'=0. The s,z terms contribute zero by the two identities above. Thus the five effective gradient rows have an exact nonzero kernel, and their rank is ≤4.

### Positive normalized multipliers exist and satisfy every equation

Choose four physical-coordinate stationarity equations, together with normalization

    4w_XA + 4w_AC + 2w_CC + 4w_ACT + 4w_AZT = 1.

The script chooses the four rows numerically, then proves that this particular 5×5 matrix is invertible by guarded interval Gaussian elimination throughout the exact root box. It encloses the unique solution and proves all five weights strictly positive. Invertibility also proves that the four selected stationarity rows are independent. Since the 28×5 equilibrium system has rank ≤4, the four selected physical rows span its row space. Appending the independent normalization row produces rank5; there is no conflict between these two rank statements. Therefore the exact solution satisfies all 28 center-coordinate equations, not merely the selected ones.

This proves exact KKT for minimizing R subject to f_k(C)≤R:

    Σ_k λ_k ∇f_k(C*) = 0,       Σ_k λ_k = 1,       λ_k≥0.

Approximate per-contact weights, for display only, are

    (0.07625642008, 0.04461409026, 0.04347530203,
     0.03300234840, 0.07438949025).

Exact interval enclosures and selected rows are in `local-sosc-certificate.json`. Neither an interval containing zero nor a numerical singular value is used to infer an exact identity.

## 3. The full mixed Hessian is positive on every critical direction

Write H=Σλ_k Hess f_k(C*), a 28×28 matrix. A first-order critical direction (v,dR) satisfies the linearized constraints and dR≤0. Multiplying the constraints by λ and using exact stationarity gives dR≥0. Hence dR=0, and each constraint with positive multiplier satisfies ∇f_k·v=0. The gauge gives v_19=0.

The integer-directed interval kernel proves, by interval LDL with every pivot strictly positive, that the full matrix

    H + 1000 Σ_(λ_k>0) ∇f_k ∇f_k^T + 1000 e_19 e_19^T

is positive definite. This includes all mixed blocks. On a critical direction the penalty terms vanish, so vᵀHv>0 whenever v≠0. The smallest certified LDL pivot lower bound is >0.06386; this is not asserted to be an eigenvalue bound.

Derivatives are generated by six-variable second-order AD per contact (four variables for a boundary pair, six for a triangle), then assembled into the complete 28-dimensional form. Root intervals use the unchanged 240-bit integer-directed kernel. Floating-point computations only propose discrete branch signs and row selections; exact interval guards validate those choices. Calibration includes mixed polynomial derivatives and a known unit-circle circumradius. Separate finite-difference calculations agree but are not the certificate.

## 4. Strict local minimality follows

For completeness, a direct SOSC argument avoids any unmentioned constraint qualification. Suppose feasible points approached the candidate with R≤R*. Normalize their increments and take a limiting unit direction. First-order feasibility, the gauge, and the KKT relations place this direction in the critical cone, with dR=0 and nonzero center component. Weighted feasibility and a second-order Taylor expansion give

    0 ≥ (1/2) δCᵀHδC + o(||δC||²).

Section3 makes the leading coefficient strictly positive on the limiting direction, a contradiction. Thus the gauged candidate is a strict local minimum for the necessary relaxation, hence for disk covering. Restoring rotations gives strict local optimality modulo rotations. Unlabeled centers only add finite permutations because the candidate sites are distinct.

## Evidence and scope

Reproduce:

    py -3 -B research-2026/next-cover-global/lead/local_sosc_certificate.py

Bearing inputs: C1167 root existence and exact contacts; C1173 implicit stationary contact curve. Files: `local-sosc-certificate.json`, `local_sosc_certificate.py`, `ROOT-ATTAINMENT.md`, `root_local_minimum.py`. The local kernel additionally certifies every other-site separation, branch sign, triangle area, interior location, boundary transversality, orbit incidence, positive weight enclosure, and LDL pivot.

The independent audit accepted the analytic rank/stationarity interface and code-to-geometric-object correspondence after correcting its C-site ordering error; its review does not extend to the separately certified explicit box. **No unrestricted global lower bound follows:** the remaining 1000 q10 and 1042 q11 graph systems still require exclusion or a sharp bound.
