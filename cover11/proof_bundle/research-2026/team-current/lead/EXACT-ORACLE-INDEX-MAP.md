# Exact canonical/raw oracle identification

Scope: C891 exact candidate and C919/C920 local carrying network versus C921 full canonical graph. This is a combinatorial/angle identity proof, not agreement of rounded angle arrays.

Let raw ring j map to canonical s=(j-2) mod9; hubs9,10 fixed. An anchor raw j is the switch of raw sites j,j+1, so maps to anchor s. Every endpoint edge maps accordingly.

The full canonical faces are hub9 fans k=0,1,2,3, hub10 fans k=4,5,6,7,8, and central faces at0,4. The raw active list is central faces at2,6, hub9 fans k=2,3,4,5 and hub10 fans k=1,6,8. Under the map these become the two central faces and canonical fans 0,1,2,3 (hub9) and8,4,6 (hub10). Thus exactly canonical hub10 fans5 and7 are absent: faces {10,5,6} and {10,7,8}. Those six constraints have zero local stress, not zero length. Their two free auxiliary nodes are absent from the carrying Dirichlet block; all eleven sites and nine active auxiliaries remain. Hence local graph has45edges/20free nodes; full has51edges/22free nodes. Extending any local stress by six zero weights gives a valid normalized nonnegative stress on the full graph. The isolated auxiliaries make full minimizers nonunique but do not change the minimized energy.

Write raw unwrapped switch angles beta_j=th_j+a_j from the exact root equations. Define gamma_0=0 and gamma_i=beta_(i+2 mod9)-beta_2+2pi*1_(i>=7) for1<=i<=8. This is the exact canonical ordered root anchor chart. If competing canonical angles are theta_i=iL-Dt_i, a simultaneous rotation aligning its canonical6 anchor with the root canonical6 anchor makes its raw8-pinned displacements

h_k=(theta_i-theta_6)-(gamma_i-gamma_6), i=(k-2) mod9, k=0,...,7.

Raw8 maps to canonical6. Fixed winding corrections cancel between competing and root configurations; thus this identity is valid on a directly containing angular box, not just at the root. It is the formula used by both direct containment kernels. Root rotations do not affect V or stress energy. These eight coordinates, with raw8 fixed to0, are exactly the local Euclidean norm chart, not the canonical0-pinned norm.

Independent rational implementation: r20-rigidity/r20_direct_patch_replay.py, source inspected and lead replay exit0 (lead/direct_patch_lead_replay.log). Its 120 selected local leaves all obey the direct containment inequality, 12 for C919 and108 for C920, with no reflected or historical patch branch required. Selection uses a saved patch marker only to identify leaves already separated from energy leaves by the full tree replay; the actual bound is recomputed from DBM and dyadic root box without trusting saved patch names.

Reflection, not needed for final leaves: raw reflection sends sites j->8-j and switches j->7-j. Canonical sites consequently map s->4-s and anchors i->3-i. Re-pin the reflected anchor0 to0: theta'_i=theta_3-theta_(3-i) using periodic lifts. Since y_i corresponds to theta_(i+1)-theta_i, this gives y'_i=y_(2-i), not y_(1-i). Thus the original lead reflection formula is correct. A contrary member flag is rejected algebraically; no lead source change is warranted.
