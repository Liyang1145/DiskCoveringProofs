# Independent review of the Heron two-edge deficit

The independent `check_sharp_independent.py` verifies the frozen scalar inequalities for every b=14,...,26 at U=228421/1000000. Its minimum conservative rational gap is at b=17 and exceeds approximately 0.0001954446. The r=23/100 negative control correctly refuses to certify b=15,...,19. The checker uses rational arithmetic, a Machin enclosure of pi, alternating Taylor bounds, and integer square-root bounds. It verifies numerical premises; the geometric normalization and abstract dual are reviewed separately in `AREA-REVIEW.md`.

## Two-edge estimate

Scale U to1 and put the common disk center at the origin. Let triangle vertices u,v,w lie in that closed unit disk. Put z=|u−v|, x=|w−u|, y=|w−v|, and s=x²+y². Let m=(u+v)/2 and h=(u−v)/2. The identities

    |m|²+|h|²=(|u|²+|v|²)/2≤1,
    s=2|w−m|²+2|h|²

give `s≤4+4√(1−z²/4)`. No common circumcircle, acute triangle, or geometric embedding of the affine dual is assumed. Because x,y,z≤2, also 0≤s≤8.

Let A be the interior-triangle area, and C1,C2 be the adjacent switching-triangle areas. Cauchy-Schwarz applied to the independent endpoint-distance bounds gives

    C1+C2 ≤ √(s(8−s))/4 ≤ 1.

If s≤4 then A≤xy/2≤s/4≤1, so A+C1+C2≤2.

If 4≤s≤8, the common-disk bound implies `z²≤Z=2s−s²/4`. Both sides are nonnegative, and Z≤s. Heron's identity gives

    16A² = 4x²y²−(s−z²)²
          ≤ s²−(s−z²)² = z²(2s−z²)
          ≤ Z(2s−Z),

where the final direction follows because v↦v(2s−v) is nondecreasing on [0,s]. Since Z(2s−Z)=s³(8−s)/16, we obtain

    A+C1+C2 ≤ (s+4) √(s(8−s))/16 = F(s).

The derivative of `(s+4)²s(8−s)` is `−4(s+4)(s²−4s−8)`. Its unique maximum on [4,8] occurs at s=2+2√3, where `F(s)²=9/4+3√3/2`. The exact comparisons √3<17321/10000 and `9/4+(3/2)(17321/10000)<(1101/500)²` prove F(s)<1101/500. This bound is also greater than2, so it covers the s≤4 case.

The former independent bound for these three faces is `(3√3/4+1)U²`. Since √3>433/250 and F<1101/500, its deficit is strictly greater than `(97/1000)U²`. The one-edge group has a separately verified deficit greater than `(19/500)U²`.

## Counting without double subtraction

The b boundary-owner centers form a simple abstract cycle. Each cycle edge has one switching triangle and exactly one adjacent interior site triangle; every interior triangle receives at most two such edges because b≥14. Assign each switching triangle to that unique interior face. If N1 and N2 faces receive one and two edges respectively, then b=N1+2N2, and the total area deficit is strictly greater than

    [(19/500)N1+(97/1000)N2]U² ≥ (19/500)bU².

The last inequality holds because 97/1000>2·19/500. Faces are grouped once; the argument does not add the same face deficit twice. It uses the abstract incidence structure and does not require its straight edges to form an embedded planar drawing.

## Scope and final inequality

The final scalar upper bound is the former Jensen area expression minus `(19/500)bU²`. The source certificate and this independent arithmetic implementation both show it is below pi for all b=14,...,26 at U=228421/1000000. Assuming the written geometric and topological argument in `AREA-REVIEW.md`, this excludes a cover at the main proof's target `11421/50000=0.22842`. The strict inequalities and domain conditions persist for sufficiently small radius increases, so the same argument with a slightly larger normalization radius also excludes U itself. Compactness of center configurations then gives `r_D(26)>228421/1000000`.

This is a new unconditional lower bound, not an exact value. It does not establish a matching lower bound for the archived candidate or discharge the historical candidate/frontier obligations. The numerical output of the .23 negative control does not imply a .23 covering exists; it only shows that this particular upper estimate cannot certify it.
