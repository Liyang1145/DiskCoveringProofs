"""Universal algebra for strict-slack generic position, not a covering gate."""

import sympy as sp

import n26_unit_cap_universal_identities as sparse


SCHEMA = "N26-universal-strict-slack-generic-position-polynomial-certificate-v1"
VARIABLES = (
    "ax", "ay", "bx", "by", "cx", "cy", "dx", "dy",
    "px", "py", "ux", "uy", "eta", "rho", "r",
)
HYPOTHESES = (
    "0<=r<rho<1",
    "the-original-finite-family-covers-every-point-of-the-closed-unit-disk",
    "1<=m<=26",
    "epsilon=(rho-r)/2>0",
    "outside-centres-first-projected-nonexpansively-onto-the-closed-unit-disk",
    "0<eta<min(epsilon/2,1/2)",
    "each-final-perturbation-from-the-shrunken-centre-has-norm<min(eta/2,epsilon/2)",
    "the-final-centres-avoid-the-finite-listed-polynomial-zero-sets",
)
SCOPE = (
    "nonzero-polynomial-zero-sets-have-empty-interior-by-the-written-induction",
    "the-finite-product-remains-nonzero-over-the-real-polynomial-integral-domain",
    "witness-evaluations-prove-polynomials-nonzero-not-continuous-covering-by-samples",
    "uniform-centre-movement-and-triangle-inequality-preserve-the-entire-closed-disk-cover",
    "remove-redundant-disks-only-after-generic-perturbation",
    "subfamilies-retain-every-listed-general-position-condition",
    "not-a-complete-triangular-dual-or-final-unrestricted-joint-acceptance",
)


def expressions():
    variables = sp.symbols(" ".join(VARIABLES), real=True)
    ax, ay, bx, by, cx, cy, dx, dy, px, py, ux, uy, eta, rho, r = variables
    an = ax*ax+ay*ay
    v1x, v1y, v2x, v2y = bx-ax, by-ay, cx-ax, cy-ay
    b1, b2 = bx*bx+by*by-an, cx*cx+cy*cy-an
    delta = v1x*v2y-v1y*v2x
    xx, yy = b1*v2y-b2*v1y, v1x*b2-v2x*b1
    incircle = sp.Matrix([
        [ax, ay, an, 1],
        [bx, by, bx*bx+by*by, 1],
        [cx, cy, cx*cx+cy*cy, 1],
        [dx, dy, dx*dx+dy*dy, 1],
    ]).det()
    degeneracies = {
        "zero-centre": an,
        "coincident-pair": v1x*v1x+v1y*v1y,
        "collinear-triple": delta,
        "cocircular-four": incircle,
        "pair-bisector-tangent-to-unit-circle": b1*b1-4*(v1x*v1x+v1y*v1y),
        "triple-bisector-intersection-on-unit-circle": xx*xx+yy*yy-4*delta*delta,
        "disk-footprint-tangent-to-unit-circle": (1+an-rho*rho)**2-4*an,
    }
    identities = {
        "movement-squared-norm": (
            (ax+ux)**2+(ay+uy)**2-an-2*(ax*ux+ay*uy)-(ux*ux+uy*uy)),
        "cauchy-schwarz-square": (
            an*(ux*ux+uy*uy)-(ax*ux+ay*uy)**2-(ax*uy-ay*ux)**2),
        "radial-shrink-norm": (
            ((1-eta)*ax)**2+((1-eta)*ay)**2-(1-eta)**2*an),
        "radial-shrink-movement": (
            ((1-eta)*ax-ax)**2+((1-eta)*ay-ay)**2-eta*eta*an),
        "half-slack-remains-strict": rho-(r+(rho-r)/2)-(rho-r)/2,
        "affine-pair-distance-difference": (
            (px-ax)**2+(py-ay)**2-(px-bx)**2-(py-by)**2
            -(2*(v1x*px+v1y*py)-b1)),
        "first-cramer-bisector": v1x*xx+v1y*yy-b1*delta,
        "second-cramer-bisector": v2x*xx+v2y*yy-b2*delta,
        "cleared-unit-circle-criterion": (
            4*delta*delta*(px*px+py*py-1)-(xx*xx+yy*yy-4*delta*delta)
            -(2*delta*px-xx)*(2*delta*px+xx)
            -(2*delta*py-yy)*(2*delta*py+yy)),
    }
    substitutions = {
        "zero-centre": {"ax": "1/4", "ay": "0"},
        "coincident-pair": {"ax": "0", "ay": "0", "bx": "1/4", "by": "0"},
        "collinear-triple": {
            "ax": "0", "ay": "0", "bx": "1/4", "by": "0", "cx": "0", "cy": "1/4"},
        "cocircular-four": {
            "ax": "0", "ay": "0", "bx": "1/4", "by": "0",
            "cx": "0", "cy": "1/4", "dx": "1/4", "dy": "1/2"},
        "pair-bisector-tangent-to-unit-circle": {
            "ax": "0", "ay": "0", "bx": "1/2", "by": "0"},
        "triple-bisector-intersection-on-unit-circle": {
            "ax": "0", "ay": "0", "bx": "1/2", "by": "0", "cx": "0", "cy": "1/2"},
        "disk-footprint-tangent-to-unit-circle": {"ax": "0", "ay": "0"},
    }
    symbol_map = dict(zip(VARIABLES, variables))
    witnesses = {}
    for name, substitution in substitutions.items():
        evaluation = sp.expand(degeneracies[name].subs({
            symbol_map[key]: sp.Rational(value) for key, value in substitution.items()}))
        justification = (
            "equals-(1-rho^2)^2>0-for-every-fixed-0<rho<1"
            if name == "disk-footprint-tangent-to-unit-circle"
            else "nonzero-exact-rational-constant")
        witnesses[name] = (substitution, evaluation, justification)
    return variables, degeneracies, identities, witnesses


def canonical():
    variables, degeneracies, identities, witnesses = expressions()
    return {
        "schema": SCHEMA, "variables": list(VARIABLES),
        "explicit_hypotheses": list(HYPOTHESES), "explicit_scope_and_bridge": list(SCOPE),
        "degeneracy_polynomials": {
            name: sparse.encode(value, variables) for name, value in degeneracies.items()},
        "zero_polynomial_identities": {
            name: sparse.encode(value, variables) for name, value in identities.items()},
        "nonzero_polynomial_witnesses": {
            name: {"substitution": substitution,
                   "exact_evaluation": sparse.encode(evaluation, variables),
                   "nonzero_justification": justification}
            for name, (substitution, evaluation, justification) in witnesses.items()},
    }


def gate(certificate):
    if (not isinstance(certificate, dict) or set(certificate) != {
            "schema", "variables", "explicit_hypotheses", "explicit_scope_and_bridge",
            "degeneracy_polynomials", "zero_polynomial_identities", "nonzero_polynomial_witnesses"}
            or certificate["schema"] != SCHEMA or certificate["variables"] != list(VARIABLES)
            or certificate["explicit_hypotheses"] != list(HYPOTHESES)
            or certificate["explicit_scope_and_bridge"] != list(SCOPE)):
        raise ValueError("strict-slack certificate changed a universal hypothesis or proof scope")
    variables, degeneracies, identities, witnesses = expressions()
    if (set(certificate["degeneracy_polynomials"]) != set(degeneracies)
            or set(certificate["zero_polynomial_identities"]) != set(identities)
            or set(certificate["nonzero_polynomial_witnesses"]) != set(witnesses)):
        raise ValueError("generic-position certificate omitted a degeneracy, identity or nonzero witness")
    for name, expected in degeneracies.items():
        actual = sparse.decode(certificate["degeneracy_polynomials"][name], variables)
        if not sp.Poly(actual-expected, *variables, domain=sp.QQ).is_zero:
            raise ValueError("generic-position polynomial changed: "+name)
        substitution, evaluation, justification = witnesses[name]
        witness = certificate["nonzero_polynomial_witnesses"][name]
        if (set(witness) != {"substitution", "exact_evaluation", "nonzero_justification"}
                or witness["substitution"] != substitution
                or witness["nonzero_justification"] != justification):
            raise ValueError("generic-position nonzero witness owner or ordered-real reason changed")
        value = sparse.decode(witness["exact_evaluation"], variables)
        if not sp.Poly(value-evaluation, *variables, domain=sp.QQ).is_zero:
            raise ValueError("generic-position exact witness evaluation changed")
        if name == "disk-footprint-tangent-to-unit-circle":
            rho = variables[VARIABLES.index("rho")]
            if sp.expand(value-(1-rho*rho)**2) != 0:
                raise ValueError("fixed-radius nonzero footprint witness failed")
        elif not value.is_Rational or value == 0:
            raise ValueError("generic-position witness is not a nonzero rational constant")
    for name, expected in identities.items():
        actual = sparse.decode(certificate["zero_polynomial_identities"][name], variables)
        if (not sp.Poly(actual-expected, *variables, domain=sp.QQ).is_zero
                or not sp.Poly(actual, *variables, domain=sp.QQ).is_zero):
            raise ValueError("universal centre-movement or Cramer identity failed: "+name)
    return {
        "universal_zero_polynomial_identities_checked": len(identities),
        "universal_degeneracy_polynomials_and_nonzero_witnesses_checked": len(degeneracies),
        "nonzero_witnesses_cover_every_fixed_radius_in_0_rho_1": True,
        "continuous_slack_and_density_argument_written_separately": True,
        "full_triangular_dual_and_final_unrestricted_joint_acceptance": False,
        "formal_machine_geometry_proof": False, "new_geometric_payments": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }
