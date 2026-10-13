# Global-closure analytic interface audit

Status: analytic inference audit by lead; the former outstanding k10 premise is now supplied by `K10-FULL-EXCLUSION.md` (C1139). Two explicitly routed independent judge launches failed without results; an alternative qwen tool returned no registered adapter. No independent review is claimed from those launches.

## Order of reductions
Start with an arbitrary putative cover at r<r*. Project all centers into D, keeping the same positive radius r. Projection can change boundary activity, but this causes no gap: classify the *projected* cover at r, not the original labels. FOUNDATIONS §§1–2 proves distance improvement and k∈{9,10,11}, including tangent disks and repeated centers. If its k is9, invoke the complete k9 theorem at this original radius immediately. Otherwise keep these projected centers fixed and increase radius to U. For fixed centers, intersection with S1 is monotone in radius, so new k≥10; the same origin/boundary argument bounds k≤11. Use C998 if new k=11, and only otherwise enter the k10 chart.

Thus it is unnecessary and would be wrong to assert projection or enlargement preserves the original active count. Neither invariance is used.

## Normalization and core
At radius U with exact k10, apply same-arc inner-root replacement only to active centers. INNER-ROOT-REDUCTION proves D-intersection inclusion and equality of the actual S1 arcs, so activity labels are now preserved. Each active radius is in [1−U,sqrt(1−U²)]; each inactive center has norm strictly less than1−U. For |p|<1−2U every ring has distance>U. Hence the two closed hub disks cover the open core; by closedness of their finite union, they cover the closed core too. Repeated hubs cause no general-position issue: d=0 is included in the nearmerge exclusion.

## Remaining chart coverage
C999 handles d≤1/10. C1113 (`STRICT-HUB-SEPARATION-LEMMA.md`) proves d<2U directly from core coverage and strict hub inactivity, with no capacity premise. This replaces the longer separated-hub/capacity dependency. For remaining d, rotation, independent axis reflections, and hub relabeling give h1=(x−s,y),h2=(x+s,y), s=d/2, x,y≥0. Reflection to x≥0 may interchange hub labels, which is harmless. Strict inactivity gives x+s<1−U, hence x<1−U−1/20. The core point (0,−a0) is nearest h1 because x,s≥0, so (x−s)²+(y+a0)²≤U², hence y≤3U−1. This proves containment in the declared closed root box, without assuming any symmetry of the original cover.

The s=U face is already removed by d≥2U. Alternatively, if x<a0, the core bisector endpoint requires U²+(y+sqrt(a0²−x²))²≤U², impossible; if x≥a0, inactivity requires x+U<1−U, i.e. x<a0, again impossible. Strict inactivity matters here; the tangent limit (s,x,y)=(U,a0,0) in a closed relaxation is not a legal k10 cover.

## Atom necessity at all legal triples
Inactive hub circles lie strictly inside D since |hj|+U<1. For a hub1 atom hj+Uv, squared distance to hub2 minus U² is 4s(s−Uv_x); the retained condition Uv_x≤s_lo makes it nonnegative uniformly over a hub box. The analogous hub2 expression is4s(s+Uv_x). For strict positivity, outward radial perturbations remain outside the other disk and inside D. For equality and0<s<U, the two equal-radius circles meet transversely: moving along the exposed arc produces nearby points strictly outside the other hub, each of which is a limit from outside both. Therefore all retained atoms belong to the finite closed union of the ten rings. Boundary atoms are also necessary because neither hub reaches S1. Coincident atoms retain their multiplicities in the measure; the nonnegative weighted union bound remains valid.

## Final premise, now discharged
If, and only if, the entire root box is a finite exact partition into independently validated infeasible or atomic leaves with no pending boxes, these arguments exclude projected/enlarged k10. C998 excludes k11; C986 excludes original k9. Combining this conditional lower bound with C985 would prove the requested unrestricted equality. The final manifest now satisfies this premise:6723 certified atomic leaves,318 independently checked prunes, zero pending, exact original-root partition and full fresh-source content binding. See `K10-FULL-EXCLUSION.md`; the unrestricted equality is asserted in `GLOBAL-SYNTHESIS.md`.
