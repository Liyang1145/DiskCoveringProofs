"""Fresh finer physical bounds preserving a previously useful diagonal.

Old certificates are parameter proposals only. The finer Taylor matrix,
positive LDL,tangent/dual support and whole-domain bound are freshly checked.
No monotonicity or numerical optimizer success is assumed.
"""

from fractions import Fraction as F

import n26_full134rod_correlated_quadratic_energy as exact
import n26_balanced_correlated_diagonal_suggestion as numerical


def suggest(kernel,matrix,lower,upper,old_certificate,radius,arcs,parts):
    if type(parts) is not int or not old_certificate["parts"] < parts <= 64:
        raise ValueError("actual finer strips rather than an unchanged old certificate required")
    certificate = {**old_certificate,"parts":parts}
    try:
        data = exact.quadratic_data(kernel,matrix,lower,upper,certificate,arcs)
    except ValueError:
        return None,None,{"old_diagonal_rejected_by_fresh_finer_LDL":True}
    point,dual,numeric = numerical.tangent_suggestion(data,matrix)
    choices = []
    for label,z,multipliers in (
        ("old-tangent-old-dual-FRESH-finer-matrix",list(map(F,old_certificate["quadratic_support_point"])),
         old_certificate["difference_dual"]),
        ("zero-tangent-zero-dual-FRESH-finer-matrix",[F(0)]*15,{"q":1,"terms":[]}),
        ("new-tangent-old-dual",point,old_certificate["difference_dual"]),
        ("new-tangent-zero-dual",point,{"q":1,"terms":[]}),
        ("new-tangent-new-exact-dual",point,dual),
    ):
        value,_ = exact.correlated_support({**data,"support_point":z},matrix,multipliers)
        choices.append((value,label,z,multipliers))
    _,label,point,dual = max(choices,key=lambda item:item[0])
    certificate = {**certificate,"quadratic_support_point":list(map(str,point)),"difference_dual":dual}
    result = exact.bound(kernel,matrix,lower,upper,certificate,radius,arcs)
    return certificate,result,{
        **numeric,"selected_fresh_exact_support_strategy":label,
        "original_diagonal_preserved_but_finer_matrix_LDL_and_support_freshly_checked":True,
        "old_bound_not_reused_or_called_a_finer_bound":True,
    }
