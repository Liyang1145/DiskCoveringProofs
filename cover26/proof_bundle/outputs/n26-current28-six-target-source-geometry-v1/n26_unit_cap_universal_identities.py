"""Exact universal polynomial relations for projection and cap domination.

No covering/ownership/source cache is imported. Ordered-real implications
and the Voronoi no-return bridge are stated separately in the proof note.
This is not the final unrestricted geometry joint acceptance.
"""

from fractions import Fraction as F

import sympy as sp


SCHEMA = "N26-universal-projection-and-closed-unit-cap-polynomial-certificate-v1"
VARIABLES = ("a", "b", "t", "s", "x", "y", "r2", "d", "u", "z", "v", "h")
FACTS = (
    "0<=r2<1", "t>0", "s>=0", "t^2+s^2=1",
    "r2-((t-a)^2+(s-b)^2)>=0",
    "r2-((t-a)^2+(-s-b)^2)>=0",
    "1-x^2-y^2>=0", "x-t>=0",
    "d>0", "2*t-2*a-d=0",
    "projection-only:u>=1", "projection-only:z<=1",
    "footprint-only:v>0", "footprint-only:2*v*h=1+v^2-r2",
)
DERIVATIONS = (
    "positive-a:2*t*a=(1-r2)+a^2+b^2+(endpoint-plus-slack+endpoint-minus-slack)/2",
    "y-range:s^2-y^2=disk-slack+(x-t)*(x+t)",
    "y-range:s>=0-and-s^2-y^2>=0-imply-s+y>=0-and-s-y>=0",
    "b>=0:cap-gap=endpoint-minus-slack+disk-slack+2*a*(x-t)+2*b*(s+y)",
    "b<=0:cap-gap=endpoint-plus-slack+disk-slack+2*a*(x-t)-2*b*(s-y)",
    "all-real-b:the-two-sign-cases-exhaust-all-values",
    "projection-gap=(u-1)^2+2*(u-1)*(1-z)>=0",
    "footprint:h>0-and-4*v^2*(h^2-(1-r2))=(v^2-(1-r2))^2>=0",
)


def expressions():
    variables = sp.symbols(" ".join(VARIABLES), real=True)
    a, b, t, s, x, y, r2, d, u, z, v, h = variables
    circle, bisector = t*t+s*s-1, 2*t-2*a-d
    plus = r2-(t-a)**2-(s-b)**2
    minus = r2-(t-a)**2-(-s-b)**2
    disk = 1-x*x-y*y
    gap = r2-(x-a)**2-(y-b)**2
    return variables, {
        "circle": circle, "bisector": bisector,
        "footprint": 2*v*h-(1+v*v-r2),
    }, {
        "positive-a": (
            2*t*a-((1-r2)+a*a+b*b+(plus+minus)/2), "circle", sp.Integer(1)),
        "closed-cap-y-bound": (
            (s*s-y*y)-(disk+(x-t)*(x+t)), "circle", sp.Integer(1)),
        "cap-gap-b-nonnegative": (
            gap-(minus+disk+2*a*(x-t)+2*b*(s+y)), "circle", sp.Integer(1)),
        "cap-gap-b-nonpositive": (
            gap-(plus+disk+2*a*(x-t)-2*b*(s-y)), "circle", sp.Integer(1)),
        "squared-distance-bisector": (
            ((x-a)**2+(y-b)**2)-((x-a-d)**2+(y-b)**2)-2*d*(x-t),
            "bisector", d),
        "projection-norm-gap": (
            ((u*u-1)-2*(u-1)*z)-(u-1)*(u+1-2*z), None, sp.Integer(0)),
        "projection-nonnegative-decomposition": (
            (u-1)*(u+1-2*z)-((u-1)**2+2*(u-1)*(1-z)), None, sp.Integer(0)),
        "circle-footprint-half-angle-bound": (
            4*v*v*(h*h-(1-r2))-(v*v-(1-r2))**2,
            "footprint", 2*v*h+(1+v*v-r2)),
    }


def encode(expression, variables):
    return [{
        "powers": list(powers), "coefficient": str(coefficient),
    } for powers, coefficient in sp.Poly(sp.expand(expression), *variables, domain=sp.QQ).terms()
            if coefficient != 0]


def decode(items, variables):
    if not isinstance(items, list) or len(items) > 200:
        raise ValueError("universal polynomial witness has an invalid bounded sparse shape")
    result, seen = sp.Integer(0), set()
    for item in items:
        if (not isinstance(item, dict) or set(item) != {"powers", "coefficient"}
                or not isinstance(item["powers"], list) or len(item["powers"]) != len(variables)
                or any(type(power) is not int or not 0 <= power <= 8 for power in item["powers"])
                or type(item["coefficient"]) not in (str, int)):
            raise ValueError("universal polynomial witness changed dimensions or coefficient type")
        powers = tuple(item["powers"])
        coefficient = F(item["coefficient"])
        if (powers in seen or coefficient == 0
                or max(abs(coefficient.numerator).bit_length(), coefficient.denominator.bit_length()) > 300):
            raise ValueError("universal polynomial witness repeated a term or has an invalid coefficient")
        seen.add(powers)
        term = sp.Rational(coefficient.numerator, coefficient.denominator)
        for variable, power in zip(variables, powers):
            term *= variable**power
        result += term
    return sp.expand(result)


def canonical():
    variables, constraints, identities = expressions()
    return {
        "schema": SCHEMA, "variables": list(VARIABLES),
        "explicit_ordered_real_hypotheses": list(FACTS),
        "explicit_sign_derivations_and_exhaustive_cases": list(DERIVATIONS),
        "zero_constraints": {name: encode(value, variables) for name, value in constraints.items()},
        "identities": {
            name: {
                "residual": encode(residual, variables), "zero_constraint": constraint,
                "constraint_multiplier": encode(multiplier, variables),
            } for name, (residual, constraint, multiplier) in identities.items()
        },
    }


def gate(certificate):
    if (not isinstance(certificate, dict) or set(certificate) != {
            "schema", "variables", "explicit_ordered_real_hypotheses",
            "explicit_sign_derivations_and_exhaustive_cases", "zero_constraints", "identities"}
            or certificate["schema"] != SCHEMA or certificate["variables"] != list(VARIABLES)
            or certificate["explicit_ordered_real_hypotheses"] != list(FACTS)
            or certificate["explicit_sign_derivations_and_exhaustive_cases"] != list(DERIVATIONS)):
        raise ValueError("universal cap certificate omitted a hypothesis/sign case or promoted its scope")
    variables, constraints, identities = expressions()
    if (set(certificate["zero_constraints"]) != set(constraints)
            or set(certificate["identities"]) != set(identities)):
        raise ValueError("universal cap certificate omitted an exact relation or proof identity")
    for name, expression in constraints.items():
        if sp.expand(decode(certificate["zero_constraints"][name], variables)-expression) != 0:
            raise ValueError("universal cap certificate changed an actual zero relation")
    for name, (residual, constraint, multiplier) in identities.items():
        item = certificate["identities"][name]
        if (set(item) != {"residual", "zero_constraint", "constraint_multiplier"}
                or item["zero_constraint"] != constraint):
            raise ValueError("universal cap identity has unknown fields or the wrong equality owner")
        actual_residual = decode(item["residual"], variables)
        actual_multiplier = decode(item["constraint_multiplier"], variables)
        expected = constraints[constraint]*actual_multiplier if constraint is not None else sp.Integer(0)
        if (sp.expand(actual_residual-residual) != 0
                or sp.expand(actual_multiplier-multiplier) != 0
                or sp.expand(actual_residual-expected) != 0):
            raise ValueError("universal cap or projection polynomial identity failed exactly")
    return {
        "universal_polynomial_identities_exactly_checked": len(identities),
        "ordered_real_hypotheses_and_both_sign_cases_explicitly_bound": True,
        "identity_checks_are_symbolic_not_finite_point_sampling": True,
        "Voronoi_irredundancy_arc_and_dual_bridge_still_requires_joint_geometry_acceptance": True,
        "formal_machine_geometry_proof": False,
        "new_geometric_payments": 0, "global_lower_bound_proved": False,
        "global_optimality_proved": False,
    }
