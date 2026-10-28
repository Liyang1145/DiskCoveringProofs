import N11Formalization.SourceExactRoot
import N11Formalization.FlashTenBoundaryTwoCircle

/-! # DSH-TOPO-C1 probe 2: API names for the exclusion assembly and the controls

Interface probe only — no theorem, no proof, no claim. Resolves the exact names of
(a) the `Fin (n+1) → Fin n` complement enumeration, (b) the subtype-cardinality lemmas,
(c) the `arcsin`/`sin` order lemmas and `π` bounds used by the counting control,
(d) the `Interval/*` namespaces (the probe-1 misses).
-/

open N11Formalization

/-! ## (a)/(b) enumerating the ten non-hub indices -/

#check @Fin.succAbove
#check @Fin.succAbove_ne
#check @Fin.succAbove_right_injective
#check @Fin.exists_succAbove_eq
#check @Fin.succAbove_eq_iff
#check @Fin.range_succAbove
#check @Fin.succAboveEmb
#check @Fintype.card_subtype_compl
#check @Fintype.card_subtype_eq
#check @Fintype.card_subtype
#check @Finset.card_filter_add_card_filter_not
#check @Fintype.card_subtype_lt

/-! ## (c) order lemmas for the counting control -/

#check @Real.lt_arcsin_iff_sin_lt
#check @Real.arcsin_lt_iff_lt_sin
#check @Real.le_arcsin_iff_sin_le
#check @Real.arcsin_le_iff_le_sin
#check @Real.sin_lt
#check @Real.sin_lt_one_of_pos
#check @Real.pi_gt_three
#check @Real.pi_lt_32_9
#check @Real.pi_gt_d20
#check @Real.sin_pos_of_pos_of_lt_pi
#check @Real.cos_le_cos_of_nonneg_of_le_pi
#check @Real.cos_lt_cos_of_nonneg_of_le_pi
#check @Real.cos_sub_int_mul_two_pi
#check @Real.cos_pi_div_ten
#check @Real.cos_two_pi_div_ten

/-! ## (d) the interval / arc-function kernel namespaces -/

#check @N11Formalization.RatInterval
#check @N11Formalization.RatInterval.Mem
#check @N11Formalization.RatInterval.sqrt
#check @N11Formalization.RatInterval.sqrtLo
#check @N11Formalization.RatInterval.sqrtHi
#check @N11Formalization.RatInterval.sinI
#check @N11Formalization.RatInterval.cosI
#check @N11Formalization.RatInterval.acosI
#check @N11Formalization.sinTQ
#check @N11Formalization.sinLo
#check @N11Formalization.sinHi
#check @N11Formalization.cosLo
#check @N11Formalization.cosHi

/-! ## (e) the two-circle capacity ingredients, to be reused verbatim -/

#check @N11Formalization.isClosed_exists_dist_le
#check @N11Formalization.Finset.sum_add_distrib
#check @N11Formalization.Finset.sum_const
#check @N11Formalization.feasibleRadii_lowerBounds
#check @N11Formalization.N11MainStatement
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
