# Round15 milestone: exact convex hub lens, not a sharp global theorem

## Target and missing implication
Original goal remains unconditional sharp n=11 optimum, cap999. Global bounds unchanged: 3/8 < r_D(11) <= C249. Current subsidiary obligation is to exclude flat sector2 on the surviving inward q0 graph. Its seven-factor objective must be bounded over the ENTIRE necessary patch domain, not only local Q0.

## Structural gains (analytic proofs)
- C855: ridge (delta=b1-b2,H=2r sin(b1+b2)) is feasible throughout the legal bearing rectangle, not only Q0. Rational convex-quadratic proof in GLOBAL-RIDGE-FEASIBILITY.md; exact arithmetic control bearing_partial_control.json. This is geometry, NOT objective maximization.
- C856: exact height-cone coordinates u=asin(H/2r),epsilon=delta-(b1-b2). Two face inequalities become |epsilon|+u<=min(T,pi-T). Hubnorm adds one acos interval. Every fixed outer tuple has one epsilon interval. See HEIGHT-CONE-EXACT-CHART.md.
- C857/C858: Cartesian hub coordinates (v,t)=(H cosdelta,H sindelta) turn the two face constraints and hubnorm into three disks. The apparent forbidden endpoint disks are externally tangent to the hubnorm disk, so separation is REDUNDANT. The full C848 fiber is convex (three disks plus a linear wedge); fixed-v sections are one interval. At T=pi/2 the two face disks COINCIDE, a necessary interface degeneracy. Proofs CARTESIAN-HUB-DISK-INTERSECTION.md and HUB-CONVEX-LENS-REDUCTION.md; exact Sympy controls cartesian_hub_control.json. Independent member core audit agrees; its final numeric floor paragraph has a typo (see audit cautions).
- WIDTH-BEARING-PARTIAL.md derives the correct partial-b sensitivity and trig-collapsed width formula. Its guarded mean-value bound preserves the full b/w dependence, unlike the rejected member recipe.
- CARTESIAN-ANGLE-CANCELLATION.md cancels the hub direction angle from the joint objective. Hub objective becomes linear area plus two simple atan2/radial terms about fixed neighboring sites. Implemented/calibrated, bounded experiment pending at milestone.

## Bounded kernel comparisons (all 1601 outer evaluations)
Same exact9decimal coefficient SHA256 5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb. Each retained all live/terminal upper bounds at budget exit. These are loose patch bounds, not exclusions:
- H-monotonicity endpoint reduction: 28.36030906849 (68 positive boxes,1499 fallback), no gain over old28.3598491. Do not scale this mechanism unchanged.
- Height-cone chart:28.31535859253.
- Correct bearing partial / collapsed width on original delta chart:28.29117981927.
- Height-cone + collapsed width:28.26079562538.
- Cartesian convex lens + collapsed width:28.24283762922.
- Cartesian angle cancellation: PID31860, patch_outer_cartesian_cancel.log/.err; result expected patch_outer_cartesian_cancel_certificate.json. Do not relaunch while active.
Each source manifest recorded at start. Point controls 104 or187 are calibration, not continuum evidence. Current kernels still need risk-proportionate interval-interface audit before promotion as bearing exclusion; no result yet near the needed threshold.

## Matching 22 factors now recomputed
Member cline2-coupled-factors ran all22 on current bytes in digest-keyed alias, no budget increase:283236 evaluations, every factor below240k cap, none budget-ended. Own output out/r15_5671967c5a3d/; member report R15-SWEEP-RESULT.md. Initial wrapper omitted face0 on an unsupported supposed proof; lead source inspection caught it BEFORE sweep, now fixed. Existing factors11/14 were same digest and retained.
Lead outward assembly (assemble_current_patch.py -> current_patch_assembly.json):
 constant = -23.44124763907495274818...
 sum22 = -1.52420512310788358144...
 constant+22 = -24.96545276218283632963...
 With C854 local J<=28.1044, total<=3.138947237817164 < pi.
 To exclude entire flat patch, need global J<28.10704541577262956809..., not merely28.24284.
The 22-factor terms are global necessary-domain bounds and CAN pair with local or global seven-factor bounds, provided scope is kept: local pairing only excludes the Q0 subfamily, not its complement. Full proof of assembly/interface is next audit before registering conditional exclusion. No full flatsector2 exclusion, no sharp global optimum.

## Rejected work / audit cautions
Metric-reduction member claimed G(b,w) b-independent and endpoint maxima; both false. acos(.38)>pi/4 also invalidated its monotonicity claim. Entire recipe withdrawn, no kernel imported it. Correct lead sensitivity above. Member later derivatives agree at formula level, but no need for a new reviewer chain.
Sharp-fan audit correctly verifies external tangency and circle degeneracy. Its floor arithmetic typo uses81/100 instead of231/250: correct sqrt(2139)/50 -231/250>0 because25*2139=53475>231²=53361. Also H=|(v,t)|, NOT |c9|. Lead analytic proofs use correct quantities.
Coupled-factors allocation diagnostic based on magnitudes is NOT a bound on reducible error; only the outward assembly is used. Source table and domain proofs, not producer claims, justify reuse.

## Next action
Inspect Cartesian angle-cancel bounded run and derive a centered support/derivative enclosure on the convex hub lens, rather than scaling unchanged grids. Audit constant+29-factor coverage and register only localQ0 exclusion if warranted. The original sharp goal remains active, unchanged.

## End-of-milestone additions
C859 localQ0exclusion nowauditedandregistered; manifestpins22records. C860 falsifiesGLOBALridge-max by>.04615 certifiedgain, twocoordinatecontrols. Thus nextwork mustboundgeneralhubpoints, notglobalizeC853. Anglecancel1601ended28.249500973; 401hubMVT28.349654; fullouterMVTfiveboxes unhelpful afterwholeextensionguardrepair. Generalradialsecantrepresentation + exactcoupledHessiancriterion documented; memberfalsepertermconcavity rejected. Alllocaljobsfinished, noheavyjobpending.

### C861 structural gain after C860
ExactLaplacianplusdistance-trianglecap establishesDelta>.3966 overb1,b2>=1. Maximumon3diskboundaries, wedgescannotbeactive. New3outer+boundarycirclefiberkernel; threepointcontrols; bounded401outerrunPID26260active. Teamsharpfan domainauditactive. Area-cancel1601finished28.237215 (stillinsufficient). Next highleveragework boundaryarccontracts andlowbearingregion, notconcavity/ridgeguess.
