import Mathlib
import N11Formalization.Definitions

namespace N11Formalization.FlashTilingProbe

open N11Formalization

#check @finRotate
#check @finRotate_apply
#check @finRotate_succ
#check @finRotate_zero
#check @finRotate_symm
#check @Fin.val_finRotate
#check @Fin.val_finRotate_succ
#check @Fin.coe_finRotate
#check @Fin.finRotate_apply

example {n : ℕ} (i : Fin n) : (finRotate n).symm (finRotate n i) = i := Equiv.symm_apply_apply _ _

example {n : ℕ} (i : Fin n) : finRotate n ((finRotate n).symm i) = i := Equiv.apply_symm_apply _ _

end N11Formalization.FlashTilingProbe
