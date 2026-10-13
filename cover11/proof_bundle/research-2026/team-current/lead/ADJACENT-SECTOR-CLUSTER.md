# Pointwise adjacent-sector cluster, replacing averaged matching

Object: actual inward q0 nine-ring cover, R0=19/50 normalization. Two consecutive sectors i,j=i+1 have (alpha_i,u,t),(alpha_j,t,v). Their shared endpoint distances are equal because the switch is a Voronoi equality point. Compute each chord width w from the cosine law and base angles L,T by the already proved sector formulas. Local cyclic closure gives exactly
 b = [pi - T_i - L_j - (w_i+w_j)/2]/2.

Thus the TWO sector factors plus their connecting switch factor have only FIVE independent variables alpha_i,u,t,alpha_j,v; switch radius t and its angle b are determined. Retain both C844 inequalities, positive width floors, b in[0,pi/2], and the new inward-switch constraint. This is a necessary local cluster domain; sufficiency for global cover is NOT asserted.

Given ANY old dual coefficients, sum the three factor objectives evaluated at these shared variables. The endpoint first- and second-matching terms cancel pointwise at the shared switch. The local circle-closure multiplier also cancels to its fixed constant (the same pi coefficient already present in the global constant); do not subtract that constant twice. This gives a rigorous replacement of the sum of three separate suprema by a joint supremum, if the latter is bounded rigorously.

For the target branch alpha_2=pi, u_2=v_2=t, its two adjacent switches have the same radius t. One may couple sector2, switches1/2, sectors1/3 into a FIVE-factor cluster. Their variables reduce to t, alpha1,u1,alpha3,v3 (five variables), with both switch angles determined by closure. Previously probe_degenerate_triplet.py only joined sector2 with switches1/2 and optimized two FREE switch angles; it did not include the neighboring sectors or pointwise circle closure. Hence this cluster adds genuine constraints absent from that failed triplet experiment.

For this conditional cluster:
 w2=2asin(R0t), L2=T2=0;
 b1=[pi-T1-(w1+w2)/2]/2,
 b2=[pi-L3-(w2+w3)/2]/2.
All old multiplier accounting is preserved simply by summing original atoms at these points. No new optimized coefficients or symmetry assumption is needed for a first diagnostic.
