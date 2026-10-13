"""NEW actual two-origin-branch grounded134-rod kernel; arithmetic only.

No old zero-row-sum/full134-only flag is forged. The virtual origin
conductance contributes mu to the radius budget and k to boundary energy.
"""

from fractions import Fraction as F


SCHEMA = "N26-distinct-full134rod-actual-origin-covering-branch-kernel-v1"


def eligible_centers(path):
    final = path["states"][-1]
    labels = {int(key):value for key,value in path["native_to_exact_candidate_labels"].items()}
    if (
        final["terminal"] is not True or final["next"] != 26 or len(final["faces"]) != 34
        or final["pending"] or sorted(labels) != list(range(26))
        or sorted(labels.values()) != list(range(26))
        or any(labels[i] != i for i in range(16))
    ):
        raise ValueError("two-origin kernel needs actual complete original26 candidate labels")
    exposed = (1<<16)-1
    for owner in range(16):
        exposed |= final["adjacency"][owner]
    from_faces = (1<<16)-1
    for face in final["faces"]:
        if face & ((1<<16)-1):
            from_faces |= face
    if exposed != from_faces:
        raise ValueError("independent face/adjacency origin exposure disagrees")
    native = [i for i in range(16,26) if not (exposed>>i&1)]
    exact = sorted(labels[i] for i in native)
    if native != [24,25] or exact != [16,25]:
        raise ValueError("this distinct full-candidate origin mode changed its exact two source owners")
    return exact


def kernel_gate(base,path,owner,multiplier):
    eligible = eligible_centers(path)
    mu = F(multiplier)
    if (
        base.get("distinct_full134rod_60free_positive_candidate_kernel") is not True
        or base.get("original_candidate_92_rod_46_free_vertex_kernel") is not None
        or base["B"] != 16 or base["vertices"] != 76 or len(base["weights"]) != 134
        or type(owner) is not int or owner not in eligible
        or not 0 <= mu <= 10**60
    ):
        raise ValueError("origin-branch kernel changed actual source/model/eligible owner or multiplier")
    scale,den = base["scale"],base["inverse_denominator"]
    J = base["inverse"]
    m,n = mu.numerator,mu.denominator
    # Free index owner is the physical center label: center vertex16+owner.
    free_owner = owner
    T = n*den+m*scale*J[free_owner][free_owner]
    if T <= 0 or J[free_owner][free_owner] <= 0:
        raise ValueError("origin-branch Sherman-Morrison denominator is not positive")
    inverse = [
        [T*J[i][j]-m*scale*J[i][free_owner]*J[free_owner][j] for j in range(60)]
        for i in range(60)
    ]
    # Direct complete identity against the actual augmented integer matrix.
    # Sparsity is only an arithmetic implementation optimization.
    for i in range(60):
        row = [(k,n*base["matrix"][16+i][16+k]) for k in range(60)
               if base["matrix"][16+i][16+k]]
        if i == free_owner:
            row.append((free_owner,m*scale))
        for j in range(60):
            if sum(value*inverse[k][j] for k,value in row) != (n*den*T if i == j else 0):
                raise ValueError("fresh exact augmented origin-ground inverse identity failed")
    harmonic_row = base["harmonic"][free_owner]
    if min(harmonic_row) < 0 or sum(harmonic_row) != den:
        raise ValueError("actual origin center base harmonic row is not a convex combination")
    original = {(i,j):value for i,j,value in base["pairs"]}
    pairs = []
    for i in range(16):
        for j in range(i+1,16):
            value = original.get((i,j),0)*T-m*scale*harmonic_row[i]*harmonic_row[j]
            if value < 0:
                raise ValueError("origin-ground Schur off-diagonal pair became negative")
            if value:
                pairs.append((i,j,value))
    constant = F(m*den,T)
    rod_sum = F(sum(base["weights"]),scale)
    return {
        "schema":SCHEMA,"B":16,"vertices":76,"physical_rods":134,
        "actual_eligible_origin_center_labels":eligible,"origin_center_label":owner,
        "origin_multiplier":mu,"original_physical_rod_weight_sum":rod_sum,
        "radius_squared_budget_weight":rod_sum+mu,
        "boundary_origin_constant":constant,"pairs":pairs,
        "energy_denominator":scale*den*T,
        "augmented_integer_inverse_identity_all3600_entries_checked":True,
        "origin_center_harmonic_row_numerators":harmonic_row,
        "original_inverse_denominator":den,
        "original_physical_ground_resistance":F(scale*J[free_owner][free_owner],den),
        "nonzero_Schur_row_sums_NOT_relabelled_as_old_zero_row_sum":True,
        "origin_multiplier_NOT_an_unlabelled135th_physical_rod":True,
        "new_origin_mode_NOT_original_full134_only_kernel":True,
    }


def point_interval(kernel,turns,arcs):
    if (
        kernel["schema"] != SCHEMA or len(turns) != 15
        or kernel.get("distinct_full134rod_60free_positive_candidate_kernel") is not None
    ):
        raise ValueError("origin point bound changed distinct kernel/angle mode")
    angles = [F(0),*map(F,turns)]
    low = high = kernel["boundary_origin_constant"]
    for i,j,weight in kernel["pairs"]:
        cosine,_ = arcs.sincos_turn(angles[j]-angles[i])
        low += F(2*weight*(arcs.SCALE-cosine[1]),kernel["energy_denominator"]*arcs.SCALE)
        high += F(2*weight*(arcs.SCALE-cosine[0]),kernel["energy_denominator"]*arcs.SCALE)
    return low,high
