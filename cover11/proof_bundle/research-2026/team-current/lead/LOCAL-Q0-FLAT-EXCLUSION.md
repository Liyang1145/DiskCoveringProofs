# Conditional local Q0 flat-sector exclusion with matching coefficients

Object: inward q0 k4 cover of unit disk, 9 boundary sites + 2 hubs, flat middle sector2. Actual r in[.379,U=.37999], b1 in[1.106,1.108],b2 in[1.068,1.071],delta in[.035,.040]. All other sites and patch widths are unrestricted subject to the original necessary conditions. This is LOCAL in the named bearing box, not WLOG for covers.

Use the existing q0 area dual: total disk area pi is at most constant + sum of the29 atom bounds. Here z50..72=0, so no inequality-multiplier sign issue; matching/angle/closure terms cancel on an actual cover. Constant from certify_q0_closure.py:110 is
 pi*(sum(z0..8)+2sum(z9..10))-pi*sum(z112..120).
Grouping does not change this constant. Joint indices {1,2,12,13,21,22,23} are exactly the seven atoms summed by exchange_joint_patch.py:13,19-22 and expanded analytically by C849/C852. No coupling constraint is added to unrelated factors. The remaining22 indices are the exact set complement.

All coefficients are exact nine-decimal literals from joint_nested_frozen.json SHA256 5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb. No old-v2 factor value reused. C854 gives the seven-factor bound28.1044 over the larger r interval[.379,.38] and the full local width/H fibers, hence over the object above.

Remaining22: member digest-keyed out/r15_5671967c5a3d/joint_patch_tight_bound_*.json. certify_joint_rest_tight.py preserves the established broad face/switch domains and C844-filtered ring domains; discarded boxes only have rigorously failed necessary filter or retain their upper in terminalmax. Full splitting covers parent with closed children; lower_probe need not be a feasible lower bound because discarded uppers are retained. Budget exit also retains all live uppers. Every output uses current digest; source/input alias audit in memberR15-SWEEP-RESULT.md. No22factor bound is restricted to Q0, so they apply in particular to it.

Directed40digit assembly in assemble_current_patch.py (binary floats read as exact already-outward recorded uppers):
 constant+sum22∈[-24.965452762182836329630301543233162870298784,-24.9654527621828363296303015432331628702947432].
 Adding exact28.1044 gives total≤3.138947237817163670369698456766837129705606<pi.
 Therefore an actual cover in the stated flatQ0 subfamily is impossible. The strict comparison has0.00264541577 margin, not a sharp-radius equality argument.

Interface calibration on CURRENT coefficients: current_seven_split_control.json,676 randomlegalpatches, directsevenatom sum versus edge/area expression error≤1.78e-14. This is a control, not the proof; algebraic atom grouping and exact cancellation provide the interface. Source audit and C844/C854 are bearing dependencies.

Remaining: every flatsector2 patch OUTSIDE Q0; then nonflatglobaloptimization/candidateisolation. Thus this excludes one local configuration class but does not prove full flatsector2 exclusion or original sharp optimum. Existing global bounds remain unchanged.

## Pinned22-block manifest
current22_manifest.json SHA2569cf2f7634b05d78d2698a5fb93d8d64529333a0c1b14def8e8a7a51d01848978 pins all22individualrecordhashes. MemberR15b-AUDIT.md confirms exactconstantcoefficient -1865395217/250000000, partition and broad-domain scope; its erroneous first-pass indexing/rounding/formula objections were corrected, no boundchange.
