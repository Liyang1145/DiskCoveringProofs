import N11Formalization.Paid16GeneralH50
import N11Formalization.Paid16GeneralH51
import N11Formalization.Paid16GeneralH52
import N11Formalization.Paid16GeneralH53
import N11Formalization.Paid16GeneralH54
import N11Formalization.Paid16GeneralH55
import N11Formalization.Paid16GeneralH56
import N11Formalization.Paid16GeneralH57

/-! Sub-aggregate 4/8: 8 packet modules, 168 ids.
Cardinality is kernel-checked on <= 168-element literal sets only. -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralNext1182S04
open Finset
noncomputable section

def ids24 : Finset (Fin 5011) := {3088,3089,3090,3091,3092,3093,3094,3095,3096,3097,3098,3099,3100,3101,3102,3103,3104,3105,3106,3107,3109}
theorem mem_ids24 (n : Fin 5011) : n ∈ ids24 ↔ n = 3088 ∨ n = 3089 ∨ n = 3090 ∨ n = 3091 ∨ n = 3092 ∨ n = 3093 ∨ n = 3094 ∨ n = 3095 ∨ n = 3096 ∨ n = 3097 ∨ n = 3098 ∨ n = 3099 ∨ n = 3100 ∨ n = 3101 ∨ n = 3102 ∨ n = 3103 ∨ n = 3104 ∨ n = 3105 ∨ n = 3106 ∨ n = 3107 ∨ n = 3109 := by
  simp only [ids24, Finset.mem_insert, Finset.mem_singleton]
theorem ids24_card : ids24.card = 21 := by decide +kernel
theorem sub24 (n : Fin 5011) (hn : n ∈ ids24) : n ∈ Paid16GeneralH50.newIDs := by
  rcases (mem_ids24 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids25 : Finset (Fin 5011) := {3110,3111,3113,3114,3115,3117,3118,3119,3120,3123,3124,3125,3127,3128,3129,3130,3131,3132,3133,3135,3136}
theorem mem_ids25 (n : Fin 5011) : n ∈ ids25 ↔ n = 3110 ∨ n = 3111 ∨ n = 3113 ∨ n = 3114 ∨ n = 3115 ∨ n = 3117 ∨ n = 3118 ∨ n = 3119 ∨ n = 3120 ∨ n = 3123 ∨ n = 3124 ∨ n = 3125 ∨ n = 3127 ∨ n = 3128 ∨ n = 3129 ∨ n = 3130 ∨ n = 3131 ∨ n = 3132 ∨ n = 3133 ∨ n = 3135 ∨ n = 3136 := by
  simp only [ids25, Finset.mem_insert, Finset.mem_singleton]
theorem ids25_card : ids25.card = 21 := by decide +kernel
theorem sub25 (n : Fin 5011) (hn : n ∈ ids25) : n ∈ Paid16GeneralH51.newIDs := by
  rcases (mem_ids25 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids26 : Finset (Fin 5011) := {3137,3138,3139,3140,3141,3142,3143,3144,3146,3147,3148,3151,3152,3153,3154,3155,3156,3157,3158,3159,3160}
theorem mem_ids26 (n : Fin 5011) : n ∈ ids26 ↔ n = 3137 ∨ n = 3138 ∨ n = 3139 ∨ n = 3140 ∨ n = 3141 ∨ n = 3142 ∨ n = 3143 ∨ n = 3144 ∨ n = 3146 ∨ n = 3147 ∨ n = 3148 ∨ n = 3151 ∨ n = 3152 ∨ n = 3153 ∨ n = 3154 ∨ n = 3155 ∨ n = 3156 ∨ n = 3157 ∨ n = 3158 ∨ n = 3159 ∨ n = 3160 := by
  simp only [ids26, Finset.mem_insert, Finset.mem_singleton]
theorem ids26_card : ids26.card = 21 := by decide +kernel
theorem sub26 (n : Fin 5011) (hn : n ∈ ids26) : n ∈ Paid16GeneralH52.newIDs := by
  rcases (mem_ids26 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids27 : Finset (Fin 5011) := {3161,3162,3163,3164,3165,3166,3167,3168,3169,3170,3171,3172,3173,3174,3175,3176,3177,3178,3179,3180,3181}
theorem mem_ids27 (n : Fin 5011) : n ∈ ids27 ↔ n = 3161 ∨ n = 3162 ∨ n = 3163 ∨ n = 3164 ∨ n = 3165 ∨ n = 3166 ∨ n = 3167 ∨ n = 3168 ∨ n = 3169 ∨ n = 3170 ∨ n = 3171 ∨ n = 3172 ∨ n = 3173 ∨ n = 3174 ∨ n = 3175 ∨ n = 3176 ∨ n = 3177 ∨ n = 3178 ∨ n = 3179 ∨ n = 3180 ∨ n = 3181 := by
  simp only [ids27, Finset.mem_insert, Finset.mem_singleton]
theorem ids27_card : ids27.card = 21 := by decide +kernel
theorem sub27 (n : Fin 5011) (hn : n ∈ ids27) : n ∈ Paid16GeneralH53.newIDs := by
  rcases (mem_ids27 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids28 : Finset (Fin 5011) := {3183,3184,3185,3186,3187,3188,3189,3190,3191,3192,3193,3194,3195,3196,3197,3198,3199,3200,3201,3202,3203}
theorem mem_ids28 (n : Fin 5011) : n ∈ ids28 ↔ n = 3183 ∨ n = 3184 ∨ n = 3185 ∨ n = 3186 ∨ n = 3187 ∨ n = 3188 ∨ n = 3189 ∨ n = 3190 ∨ n = 3191 ∨ n = 3192 ∨ n = 3193 ∨ n = 3194 ∨ n = 3195 ∨ n = 3196 ∨ n = 3197 ∨ n = 3198 ∨ n = 3199 ∨ n = 3200 ∨ n = 3201 ∨ n = 3202 ∨ n = 3203 := by
  simp only [ids28, Finset.mem_insert, Finset.mem_singleton]
theorem ids28_card : ids28.card = 21 := by decide +kernel
theorem sub28 (n : Fin 5011) (hn : n ∈ ids28) : n ∈ Paid16GeneralH54.newIDs := by
  rcases (mem_ids28 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids29 : Finset (Fin 5011) := {3204,3205,3206,3207,3208,3209,3210,3211,3212,3213,3214,3215,3216,3217,3218,3219,3220,3221,3222,3223,3224}
theorem mem_ids29 (n : Fin 5011) : n ∈ ids29 ↔ n = 3204 ∨ n = 3205 ∨ n = 3206 ∨ n = 3207 ∨ n = 3208 ∨ n = 3209 ∨ n = 3210 ∨ n = 3211 ∨ n = 3212 ∨ n = 3213 ∨ n = 3214 ∨ n = 3215 ∨ n = 3216 ∨ n = 3217 ∨ n = 3218 ∨ n = 3219 ∨ n = 3220 ∨ n = 3221 ∨ n = 3222 ∨ n = 3223 ∨ n = 3224 := by
  simp only [ids29, Finset.mem_insert, Finset.mem_singleton]
theorem ids29_card : ids29.card = 21 := by decide +kernel
theorem sub29 (n : Fin 5011) (hn : n ∈ ids29) : n ∈ Paid16GeneralH55.newIDs := by
  rcases (mem_ids29 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids30 : Finset (Fin 5011) := {3225,3226,3227,3228,3229,3230,3231,3232,3233,3234,3235,3236,3237,3238,3239,3240,3241,3242,3243,3244,3245}
theorem mem_ids30 (n : Fin 5011) : n ∈ ids30 ↔ n = 3225 ∨ n = 3226 ∨ n = 3227 ∨ n = 3228 ∨ n = 3229 ∨ n = 3230 ∨ n = 3231 ∨ n = 3232 ∨ n = 3233 ∨ n = 3234 ∨ n = 3235 ∨ n = 3236 ∨ n = 3237 ∨ n = 3238 ∨ n = 3239 ∨ n = 3240 ∨ n = 3241 ∨ n = 3242 ∨ n = 3243 ∨ n = 3244 ∨ n = 3245 := by
  simp only [ids30, Finset.mem_insert, Finset.mem_singleton]
theorem ids30_card : ids30.card = 21 := by decide +kernel
theorem sub30 (n : Fin 5011) (hn : n ∈ ids30) : n ∈ Paid16GeneralH56.newIDs := by
  rcases (mem_ids30 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids31 : Finset (Fin 5011) := {3246,3247,3248,3249,3250,3251,3252,3253,3254,3255,3256,3257,3258,3259,3260,3261,3262,3263,3264,3265,3266}
theorem mem_ids31 (n : Fin 5011) : n ∈ ids31 ↔ n = 3246 ∨ n = 3247 ∨ n = 3248 ∨ n = 3249 ∨ n = 3250 ∨ n = 3251 ∨ n = 3252 ∨ n = 3253 ∨ n = 3254 ∨ n = 3255 ∨ n = 3256 ∨ n = 3257 ∨ n = 3258 ∨ n = 3259 ∨ n = 3260 ∨ n = 3261 ∨ n = 3262 ∨ n = 3263 ∨ n = 3264 ∨ n = 3265 ∨ n = 3266 := by
  simp only [ids31, Finset.mem_insert, Finset.mem_singleton]
theorem ids31_card : ids31.card = 21 := by decide +kernel
theorem sub31 (n : Fin 5011) (hn : n ∈ ids31) : n ∈ Paid16GeneralH57.newIDs := by
  rcases (mem_ids31 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def newIDs : Finset (Fin 5011) := ids24 ∪ (ids25 ∪ (ids26 ∪ (ids27 ∪ (ids28 ∪ (ids29 ∪ (ids30 ∪ (ids31)))))))
theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ n ∈ ids24 ∨ n ∈ ids25 ∨ n ∈ ids26 ∨ n ∈ ids27 ∨ n ∈ ids28 ∨ n ∈ ids29 ∨ n ∈ ids30 ∨ n ∈ ids31 := by
  simp only [newIDs, Finset.mem_union]
theorem new_count : newIDs.card = 168 := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH50.new_terminal n (sub24 n h)
  · exact Paid16GeneralH51.new_terminal n (sub25 n h)
  · exact Paid16GeneralH52.new_terminal n (sub26 n h)
  · exact Paid16GeneralH53.new_terminal n (sub27 n h)
  · exact Paid16GeneralH54.new_terminal n (sub28 n h)
  · exact Paid16GeneralH55.new_terminal n (sub29 n h)
  · exact Paid16GeneralH56.new_terminal n (sub30 n h)
  · exact Paid16GeneralH57.new_terminal n (sub31 n h)
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH50.new_radius n (sub24 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH51.new_radius n (sub25 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH52.new_radius n (sub26 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH53.new_radius n (sub27 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH54.new_radius n (sub28 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH55.new_radius n (sub29 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH56.new_radius n (sub30 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH57.new_radius n (sub31 n h) y hy0 hy1 hc C Z r hf
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
end
end N11Formalization.Paid16GeneralNext1182S04
#print axioms N11Formalization.Paid16GeneralNext1182S04.new_count
#print axioms N11Formalization.Paid16GeneralNext1182S04.new_radius
