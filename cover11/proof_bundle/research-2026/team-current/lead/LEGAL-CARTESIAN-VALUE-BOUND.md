# Feasible-value enclosure distinct from full-extension derivative enclosure

For C858 legal hub X=(v,t), source Q_j=(r sin2b_j,∓2r sin²b_j) with Cartesian argument X_j=v-r sin2b, Y_j=2r sin²b+sigma t (sigma=-1,+1), own face disk implies Y_j≥0 by its vertical cap (NOT merely wedge). Source Q_j is on own face circle, so distance |X-Q_j|≤2r and e=|X-Q_j|/(2R0)≤r/R0. These are necessary value constraints only.

legal_cartesian_value.py intersects Y with[0,∞), e with[0,r/R0]. If a box contains the angle origin, enclose angle in[0,pi]. Each frozen radial term bb*e²+gg*e has bb>0, so its maximum on the interval e∈[l,u] is at l or u; directed endpoint evaluation bounds it without cancellation loss. Linear and angle terms are separately interval bounded, plus exact C872 width endpoints.

THIS DOES NOT SUPPLY DERIVATIVES. The full-extension AD and Taylor enclosures retain their original smooth domains and refuse at poles. The feasible-value bound can be intersected only with final upper bounds; it is never inserted into AD intermediates. This permits direct value exclusion even on boxes whose analytic extension encounters a pole although legal objective values are bounded.

12 legal corner point controls in legal_cartesian_value_control.json compare independent Cartesian enclosure with low_corner_jet objective. These are calibration; enclosure validity is the preceding geometry+convex quadratic argument.
