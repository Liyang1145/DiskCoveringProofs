# Nonzero anchor radius and a possible radial slab control

Immediate rigorous consequence at fixed U normalized representation: every boundaryanchor radius a>=1−sqrt(1−U²)>0, uniformly, since |A|=1 and |site|<=sqrt(1−U²). Thus anchor-radius zero is not a genuine-cover degeneration, although current permissive relaxations allow it. At U=.331732..., lowera≈.05662634, normalized y≥.1707. Faces may still have zero radii in a limit; no lowerbound on realface radius is inferred.

The boundarycone inequality in BOUNDARY-ANCHOR-NORM-CONSTRAINT.md strengthens as a shrinks: cosgammaA >= (a²+U²)/(2a). Near minimal a, gammaA→0, so boundarysiteedge length l=2a singammaA shrinks. A useful polynomial upper on edge length follows:
 l² <= 4a²−(a²+U²)².
This is exact: l²=4a²sin²gammaA and squarecone inequality. It equals the maximal separation of two points in normdisk(s) at equal distancea fromaunitanchor; endpoints ofcircleintersection attainit. At a=U, l<=2U sqrt(1−U²). At a=1−s, l=0.

Interpretation: small anchorradii force short boundaryedges, not just smallpairedarea. Togetherwithfixedqperimeter andtriangleedgelengthcompatibility thismaypenalizeanchor deficits. No global lowerbound claimed; nextkernel shouldkeep sharedanchorvariables ratherthan discardthembeforeoptimizingfaceareas.
