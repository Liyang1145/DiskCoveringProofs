# Scalar network energy as an independent cell lower bound

Object: same 51-edge anchored graph; V(U)=min_free max_e |X_v-X_w|. For every exact rational alpha_e>=0, sum alpha=1,

V(U)^2 >= E_alpha(U):=min_free sum_e alpha_e |X_v-X_w|^2.

No equilibrium at a saved site configuration is needed. Alpha must be scalar; the vector-force norm budget is a distinct dual.

When every free component meets an anchor through positive-alpha edges, the free Laplacian Lff is SPD. Eliminating it gives Lambda=Laa-Laf Lff^-1 Lfa, a graph Laplacian on the anchors with nonpositive offdiagonal entries. Thus for exact rational w_ij=-Lambda_ij>=0,

E_alpha(U(theta)) = sum_(i<j) 2 w_ij (1-cos(theta_i-theta_j)).

The Schur identity may be certified by exact rational inversion and its row sums/offdiagonal signs; solver output is only an alpha proposal.

For a simplex theta(lambda)=sum lambda_v theta^(v), put z_ij=theta_i-theta_j. Term g_ij(z)=2w_ij(1-cos z) has second derivative 2w_ij cos z. If c_ij >= max_interval(0,2w_ij cos z), then g_ij(z)-c_ij z^2/2 is concave. Consequently

E_alpha(theta(lambda)) >= sum_v lambda_v E_alpha(theta^(v)) - sum_(i<j) c_ij range(z_ij)^2/8.

The sign here is intentionally different from fixed-vector support curvature: subtract an UPPER bound on E'' to get concavity. Correlated differences z_ij should be ranged directly over vertices, not by separate theta_i/theta_j intervals.

Any collection of these energy rows admits the same rational-beta matrix game bound as the vector-support rows. Units are V^2, and threshold is (19/50)^2 or an appropriate bound on R*^2. They cannot be mixed in a matrix with V-unit rows without a justified conversion.

Purpose of next bounded experiment: compare this rotation-invariant pair-difference lower bound to stored vector-support tree leaves. A positive result may improve angular overestimation; a negative result only identifies the representation's loss. No global certificate is asserted here.
