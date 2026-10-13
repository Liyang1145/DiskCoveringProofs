# Rigorous edge deficit and face imbalance inequality

Analytic proof, global necessary metric constraint for interiorDelaunayedges, unitD, coveringradius<=U. β∈(0,π), incidentfaceanglesγf,γg>0, radiiRf,Rg∈(0,U]. Let Δ=(γf−γg)/2 and x=Rf/U,y=Rg/U. Then γf+γg=π−β, sharededge equality gives

 τ=|x−y|/(x+y)=|tanΔ|tan(β/2)∈[0,1).

Since max(x,y)<=1, xy<=min(x,y)/max(x,y)=(1−τ)/(1+τ). The gap between relaxed and actual pairedfacetarea is

 D_e=U²(1−xy)sinβ
 >=U²[2τ/(1+τ)]sinβ
 >=U² τ sinβ
 =U²(1−cosβ)|tanΔ|
 >=U²(1−cosβ)|Δ|.

The inequality passesβ=0 limits trivially(D_e>=0); positiveβ version requiresordinarynondegeneratefaces, withcompactlimitslater. β=π occurs onlylimitingdegeneracy, and handledbylimitofpreviousinequality ifΔ→0.

For a dualtriangle f whose3edges areinterior, define Δ_fe=γ_fe−(π−β_e)/2. Itsangles sumπ, hence

 Σ_{e⊂f} Δ_fe=(Σ_{e⊂f}β_e−π)/2.

If eachβ_e>=b0>0, then
 Σ_{e⊂f}D_e >=(U²/2)(1−cos b0)|Σβ_e−π|.

For arbitraryfaces usem_f=min_{e⊂f}(1−cosβ_e): sameboundwithm_f. Summingoverfacescounts eachedgeatmosttwice, so totalfacetdeficit>=U²/4 Σ_f m_f|Σβ_e−π|. For a singlechosenface nofactor2loss.

This is a genuine omittedmetricconstraint: it linksfaceangle imbalance to lossinarea, whereas oldlinearangleextensionsalone canhavearbitraryradii. It doesnot yetcertify anygraph becauseβcoordinates canmove andm_f canvanish. Next: use a smallangleboxpartition or derive a convex lowerenvelope of theweightedabsoluteimbalance, notapplypointdefectsasglobalbounds.

Calibration `radius-saturation-probe.json`:12closestjointsurvivorDUALtangencyproposals havefaceimbalance0.33..2.50radians. These are notprimalfeasibleangleassignments; diagnostic suggestsleverage, notproof.
