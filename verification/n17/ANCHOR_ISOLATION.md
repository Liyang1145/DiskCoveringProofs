<!-- SPDX-License-Identifier: MIT -->
# n=17: exact native candidate-anchor isolation

**Scope.** The result excludes a strict improvement for this 63-rod
candidate graph in an anchor neighborhood only. It is not a proof of
the candidate angle-domain complement or of another topology. The
graph must be matched to its labeled anchor/face incidences before
applying this neighborhood.

Let \(q_0=(1,0)\), and write \(y_*\) for the other 82 Cartesian
coordinates of the fixed algebraic root accepted by
[the native root checker](../../tools/check_native_n17_root.py).
Its stationary equations use the 63 positive rod weights \(w_e\)
and 11 circle multipliers \(\mu_i\). All 63 candidate rods have
squared length \(t_*\), the same radius coordinate as in the
[attainment proof](../../docs/DISKCOVER_NATIVE_N17.md).
The algorithm was adapted from the
[native n16 isolation replay](../n16/anchor_isolation.py);
[n17 reference §10](https://github.com/VonEquinox/DiskCoveringSolve/blob/089584973f41e6374ce110f6e5b5ee456df19352/cover17/docs/r17_proof_zh.md)
supplied the parameters. No upstream matrix or acceptance routine
is used.

## Exact positive matrix

Let \(M\) be the weighted rod Laplacian with the circle multiplier
diagonal terms added, restricted to the free coordinates. Let \(A\)
be the Jacobian of the 63 squared-length constraints and 11 unit
circle equations with respect to those coordinates. Let \(P\) project
onto the 22 free anchor coordinates and \(W\) be diagonal with entries
\(w_e^2\) for rods and \(\nu^2\) for circles, where \(\nu=11/1000\).
The checker establishes \(0<w_e<1/10\), \(-\nu<\mu_i<0\), and
\[
 H=M+600A^{\mathsf T}WA-(17/10000)P\succ0.
\]

The pinned root data are checked with the native contraction proof
before extracting a center box of radius \(10^{-80}\). Round its
geometry and multipliers to denominator \(Q=10^{15}\) and verify
coordinatewise error \(<\varepsilon=2/Q\).
The rounded geometric Jacobian has Frobenius norm \(<10\).
Each rod row has at most four entries moving by \(4\varepsilon\)
and each circle row at most two entries moving by \(2\varepsilon\),
so an operator perturbation bound is \(\delta_A=400\varepsilon\).
If the rod graph degree is at most \(\Delta\), the max absolute row
sum gives \(\delta_M=(2\Delta+1)\varepsilon\). For the diagonal weights,
\(\delta_W=\varepsilon/4\) suffices because
\(\lvert w^2-\bar w^2\rvert\le\lvert w+\bar w\rvert\varepsilon\)
and both weights are \(<1/10\). The exact matrix error is bounded by
\[
 \delta_M+
 600\left[(20+\delta_A)\delta_A/100+
               \delta_W(10+\delta_A)^2\right]<10^{-8}.
\]
The replay subtracts \(10^{-8}I\) from the rounded matrix,
scales it by \(Q^4\), and uses exact symmetric Bareiss elimination.
Each computed leading principal determinant is strictly positive,
with every nontrivial Bareiss division exact. Thus Sylvester's
criterion and the error comparison prove the displayed matrix
strictly positive at the algebraic root.

## Exclusion without assumptions on the remaining coordinates

For a competing realization let \(d=y-y_*\) and
\(\alpha^2=d^{\mathsf T}Pd\); suppose all anchors stay on the
unit circle and all rods have squared length at most \(t_*\).
For a rod let \(s_e=t_*-\ell_e^2\ge0\) and
\(v_e=|d_u-d_v|^2\ge0\); for an anchor let \(u_i=|d_{q_i}|^2\).
The quadratic identities give
\((Ad)_e=-(v_e+s_e)\) and \((Ad)_i=-u_i\).
Stationarity at \(y_*\), dotted with \(d\), yields
\[
 \sum_e w_e(v_e+s_e)=\sum_i(-\mu_i)u_i\le\nu\alpha^2.
\]
It follows that
\(d^{\mathsf T}Md=-\sum_e w_e s_e\le0\).
The weighted squares of the rod-row linearizations sum to at most
\(\nu^2\alpha^4\), since their unsigned weighted magnitudes are
nonnegative and sum to at most \(\nu\alpha^2\). Square the
nonnegative anchor deviations and use their sum \(\alpha^2\)
to obtain another upper bound \(\nu^2\alpha^4\).
Consequently
\[
 d^{\mathsf T}H d\le
 1200\nu^2\alpha^4-(17/10000)\alpha^2.
\]
For \(\alpha\le27/250\) this is nonpositive, since
\(17/10000-1200(11/1000)^2(27/250)^2=499/78125000>0\).
Positive definiteness forces \(d=0\), even when \(\alpha=0\).
Thus no strict improvement is possible anywhere in that anchor
neighborhood, and we made no proximity assumption on its centers or
face witnesses.

## Replay

```sh
python verification/n17/anchor_isolation.py /path/to/root17.json
```

Fresh replay: 63 positive rods, 82 positive leading principal
determinants, perturbation less than \(10^{-8}\), checked bound
\(27/250\). An altered input digest is rejected before root processing.
