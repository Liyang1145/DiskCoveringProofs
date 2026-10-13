# B17 inward-owner constraint with a distinct origin-ground energy kernel

This is an arithmetic lemma for the necessary rod model, not an admission or
global n26 proof. The B17 nine-disk core argument in the separately registered
proof gives at least one boundary owner i with |c_i| <= K and ownership gap
less than a, where K=165933607/207000000 and a=9/200 turns. Its external
nine-disk radius theorem is explicitly imported there, not reproved here.

The current graph has anchor j joined to centers j and (j+1) mod 17.
Thus owner i>0 has gap theta_i-theta_(i-1); owner 0 has wrap gap
1-theta_16. A true B17 cover lies in the UNION of all seventeen branches
with |c_i|<=K and the corresponding gap<=a. No overlap is a disjoint payment.
Only already introduced centers and present triangular witnesses are used.

For positive original rod weights w_e and an additional multiplier mu>=0,
define E=sum_e w_e |p_u-p_v|^2. On branch i, at radius rho<=r,

E + mu(|c_i|^2-K^2) <= E <= r^2 sum_e w_e.

Let L be the original rod Laplacian, G its free-free block, and e_i the free
coordinate of center i. The augmented free block is G+mu e_i e_i^T. It is
positive definite: the original connected positive rod graph is already
grounded by its circle anchors, and the extra term is nonnegative. A fresh
exact inverse is computed and checked against this augmented block.

Writing L_aug for L with that free diagonal increment, H=-G_aug^-1 L_fa,
and S=L_aa-L_af G_aug^-1 L_fa, exact square completion gives

p^T L_aug p = A^T S A + (x-HA)^T G_aug (x-HA)

in each Cartesian coordinate. The checker verifies symmetry, nonpositive
off-diagonal entries and nonnegative Schur row sums. In contrast to the old
harmonic kernel, those row sums generally DO NOT vanish. If q_i=sum_j S_ij,

A^T S A = sum_(i<j) (-S_ij)|A_i-A_j|^2 + sum_i q_i |A_i|^2.

The unit anchors have |A_i|=1, so their second term is the constant sum_i q_i.
The valid boundary lower energy therefore includes BOTH that constant and
-mu K^2. The radius cap uses ONLY sum_e w_e, never sum_e w_e+mu. The extra
origin edge is a Lagrange multiplier, not a physical rho-bounded rod.

Pairwise affine minorants of 2(1-cos(2*pi*(theta_j-theta_i))) are reused only
as scalar mathematical lemmas. Their intervals use the ORIGINAL D=10^7
domain scale, not the separate sharp-angle scale 10^40. Mixtures are checked
nonnegative and exactly normalized; difference multipliers are nonnegative
and the remaining linear objective is minimized on its enclosing closed box.
This supplies a whole-branch lower bound, not a sampled-point inference.

The new module has its own schema and gates. It does not forge old harmonic
convex-combination, zero-row-sum, B16/full134 or old92 model flags. Numerical
optimizers propose weights/duals only; exact identities and rational bounds
make all arithmetic decisions. A strict branch alone does not pay a state:
all seventeen branches, including all nonempty remainders, must be covered
and independently checked before any future source admission.
