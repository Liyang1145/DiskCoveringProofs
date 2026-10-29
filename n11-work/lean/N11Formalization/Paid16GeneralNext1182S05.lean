import N11Formalization.Paid16GeneralH58
import N11Formalization.Paid16GeneralH59
import N11Formalization.Paid16GeneralH60
import N11Formalization.Paid16GeneralH61
import N11Formalization.Paid16GeneralH62
import N11Formalization.Paid16GeneralH63
import N11Formalization.Paid16GeneralH64
import N11Formalization.Paid16GeneralH65

/-! Sub-aggregate 5/8: 8 packet modules, 168 ids.
Cardinality is kernel-checked on <= 168-element literal sets only. -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralNext1182S05
open Finset
noncomputable section

def ids32 : Finset (Fin 5011) := {3267,3268,3269,3270,3271,3272,3273,3274,3275,3276,3277,3278,3279,3280,3281,3282,3283,3284,3285,3286,3287}
theorem mem_ids32 (n : Fin 5011) : n ∈ ids32 ↔ n = 3267 ∨ n = 3268 ∨ n = 3269 ∨ n = 3270 ∨ n = 3271 ∨ n = 3272 ∨ n = 3273 ∨ n = 3274 ∨ n = 3275 ∨ n = 3276 ∨ n = 3277 ∨ n = 3278 ∨ n = 3279 ∨ n = 3280 ∨ n = 3281 ∨ n = 3282 ∨ n = 3283 ∨ n = 3284 ∨ n = 3285 ∨ n = 3286 ∨ n = 3287 := by
  simp only [ids32, Finset.mem_insert, Finset.mem_singleton]
theorem ids32_card : ids32.card = 21 := by decide +kernel
theorem sub32 (n : Fin 5011) (hn : n ∈ ids32) : n ∈ Paid16GeneralH58.newIDs := by
  rcases (mem_ids32 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids33 : Finset (Fin 5011) := {3288,3289,3290,3291,3292,3293,3294,3295,3296,3297,3298,3299,3300,3301,3302,3303,3304,3305,3306,3307,3308}
theorem mem_ids33 (n : Fin 5011) : n ∈ ids33 ↔ n = 3288 ∨ n = 3289 ∨ n = 3290 ∨ n = 3291 ∨ n = 3292 ∨ n = 3293 ∨ n = 3294 ∨ n = 3295 ∨ n = 3296 ∨ n = 3297 ∨ n = 3298 ∨ n = 3299 ∨ n = 3300 ∨ n = 3301 ∨ n = 3302 ∨ n = 3303 ∨ n = 3304 ∨ n = 3305 ∨ n = 3306 ∨ n = 3307 ∨ n = 3308 := by
  simp only [ids33, Finset.mem_insert, Finset.mem_singleton]
theorem ids33_card : ids33.card = 21 := by decide +kernel
theorem sub33 (n : Fin 5011) (hn : n ∈ ids33) : n ∈ Paid16GeneralH59.newIDs := by
  rcases (mem_ids33 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids34 : Finset (Fin 5011) := {3309,3310,3311,3312,3313,3314,3315,3316,3317,3318,3319,3320,3321,3322,3323,3324,3325,3326,3327,3328,3329}
theorem mem_ids34 (n : Fin 5011) : n ∈ ids34 ↔ n = 3309 ∨ n = 3310 ∨ n = 3311 ∨ n = 3312 ∨ n = 3313 ∨ n = 3314 ∨ n = 3315 ∨ n = 3316 ∨ n = 3317 ∨ n = 3318 ∨ n = 3319 ∨ n = 3320 ∨ n = 3321 ∨ n = 3322 ∨ n = 3323 ∨ n = 3324 ∨ n = 3325 ∨ n = 3326 ∨ n = 3327 ∨ n = 3328 ∨ n = 3329 := by
  simp only [ids34, Finset.mem_insert, Finset.mem_singleton]
theorem ids34_card : ids34.card = 21 := by decide +kernel
theorem sub34 (n : Fin 5011) (hn : n ∈ ids34) : n ∈ Paid16GeneralH60.newIDs := by
  rcases (mem_ids34 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids35 : Finset (Fin 5011) := {3330,3331,3332,3333,3334,3335,3336,3337,3338,3339,3340,3341,3342,3343,3344,3345,3346,3347,3348,3349,3350}
theorem mem_ids35 (n : Fin 5011) : n ∈ ids35 ↔ n = 3330 ∨ n = 3331 ∨ n = 3332 ∨ n = 3333 ∨ n = 3334 ∨ n = 3335 ∨ n = 3336 ∨ n = 3337 ∨ n = 3338 ∨ n = 3339 ∨ n = 3340 ∨ n = 3341 ∨ n = 3342 ∨ n = 3343 ∨ n = 3344 ∨ n = 3345 ∨ n = 3346 ∨ n = 3347 ∨ n = 3348 ∨ n = 3349 ∨ n = 3350 := by
  simp only [ids35, Finset.mem_insert, Finset.mem_singleton]
theorem ids35_card : ids35.card = 21 := by decide +kernel
theorem sub35 (n : Fin 5011) (hn : n ∈ ids35) : n ∈ Paid16GeneralH61.newIDs := by
  rcases (mem_ids35 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids36 : Finset (Fin 5011) := {3351,3352,3353,3354,3355,3356,3357,3358,3359,3360,3361,3362,3363,3364,3365,3366,3367,3368,3369,3370,3371}
theorem mem_ids36 (n : Fin 5011) : n ∈ ids36 ↔ n = 3351 ∨ n = 3352 ∨ n = 3353 ∨ n = 3354 ∨ n = 3355 ∨ n = 3356 ∨ n = 3357 ∨ n = 3358 ∨ n = 3359 ∨ n = 3360 ∨ n = 3361 ∨ n = 3362 ∨ n = 3363 ∨ n = 3364 ∨ n = 3365 ∨ n = 3366 ∨ n = 3367 ∨ n = 3368 ∨ n = 3369 ∨ n = 3370 ∨ n = 3371 := by
  simp only [ids36, Finset.mem_insert, Finset.mem_singleton]
theorem ids36_card : ids36.card = 21 := by decide +kernel
theorem sub36 (n : Fin 5011) (hn : n ∈ ids36) : n ∈ Paid16GeneralH62.newIDs := by
  rcases (mem_ids36 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids37 : Finset (Fin 5011) := {3372,3373,3374,3375,3376,3377,3378,3379,3380,3381,3382,3383,3384,3385,3386,3387,3388,3389,3390,3391,3392}
theorem mem_ids37 (n : Fin 5011) : n ∈ ids37 ↔ n = 3372 ∨ n = 3373 ∨ n = 3374 ∨ n = 3375 ∨ n = 3376 ∨ n = 3377 ∨ n = 3378 ∨ n = 3379 ∨ n = 3380 ∨ n = 3381 ∨ n = 3382 ∨ n = 3383 ∨ n = 3384 ∨ n = 3385 ∨ n = 3386 ∨ n = 3387 ∨ n = 3388 ∨ n = 3389 ∨ n = 3390 ∨ n = 3391 ∨ n = 3392 := by
  simp only [ids37, Finset.mem_insert, Finset.mem_singleton]
theorem ids37_card : ids37.card = 21 := by decide +kernel
theorem sub37 (n : Fin 5011) (hn : n ∈ ids37) : n ∈ Paid16GeneralH63.newIDs := by
  rcases (mem_ids37 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids38 : Finset (Fin 5011) := {3393,3394,3395,3396,3397,3398,3399,3400,3401,3402,3403,3404,3405,3406,3407,3408,3409,3410,3411,3412,3413}
theorem mem_ids38 (n : Fin 5011) : n ∈ ids38 ↔ n = 3393 ∨ n = 3394 ∨ n = 3395 ∨ n = 3396 ∨ n = 3397 ∨ n = 3398 ∨ n = 3399 ∨ n = 3400 ∨ n = 3401 ∨ n = 3402 ∨ n = 3403 ∨ n = 3404 ∨ n = 3405 ∨ n = 3406 ∨ n = 3407 ∨ n = 3408 ∨ n = 3409 ∨ n = 3410 ∨ n = 3411 ∨ n = 3412 ∨ n = 3413 := by
  simp only [ids38, Finset.mem_insert, Finset.mem_singleton]
theorem ids38_card : ids38.card = 21 := by decide +kernel
theorem sub38 (n : Fin 5011) (hn : n ∈ ids38) : n ∈ Paid16GeneralH64.newIDs := by
  rcases (mem_ids38 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids39 : Finset (Fin 5011) := {3414,3415,3416,3417,3418,3419,3421,3423,3424,3425,3426,3427,3428,3429,3430,3435,3437,3438,3439,3441,3445}
theorem mem_ids39 (n : Fin 5011) : n ∈ ids39 ↔ n = 3414 ∨ n = 3415 ∨ n = 3416 ∨ n = 3417 ∨ n = 3418 ∨ n = 3419 ∨ n = 3421 ∨ n = 3423 ∨ n = 3424 ∨ n = 3425 ∨ n = 3426 ∨ n = 3427 ∨ n = 3428 ∨ n = 3429 ∨ n = 3430 ∨ n = 3435 ∨ n = 3437 ∨ n = 3438 ∨ n = 3439 ∨ n = 3441 ∨ n = 3445 := by
  simp only [ids39, Finset.mem_insert, Finset.mem_singleton]
theorem ids39_card : ids39.card = 21 := by decide +kernel
theorem sub39 (n : Fin 5011) (hn : n ∈ ids39) : n ∈ Paid16GeneralH65.newIDs := by
  rcases (mem_ids39 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def newIDs : Finset (Fin 5011) := ids32 ∪ (ids33 ∪ (ids34 ∪ (ids35 ∪ (ids36 ∪ (ids37 ∪ (ids38 ∪ (ids39)))))))
theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ n ∈ ids32 ∨ n ∈ ids33 ∨ n ∈ ids34 ∨ n ∈ ids35 ∨ n ∈ ids36 ∨ n ∈ ids37 ∨ n ∈ ids38 ∨ n ∈ ids39 := by
  simp only [newIDs, Finset.mem_union]
theorem new_count : newIDs.card = 168 := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH58.new_terminal n (sub32 n h)
  · exact Paid16GeneralH59.new_terminal n (sub33 n h)
  · exact Paid16GeneralH60.new_terminal n (sub34 n h)
  · exact Paid16GeneralH61.new_terminal n (sub35 n h)
  · exact Paid16GeneralH62.new_terminal n (sub36 n h)
  · exact Paid16GeneralH63.new_terminal n (sub37 n h)
  · exact Paid16GeneralH64.new_terminal n (sub38 n h)
  · exact Paid16GeneralH65.new_terminal n (sub39 n h)
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH58.new_radius n (sub32 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH59.new_radius n (sub33 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH60.new_radius n (sub34 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH61.new_radius n (sub35 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH62.new_radius n (sub36 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH63.new_radius n (sub37 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH64.new_radius n (sub38 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH65.new_radius n (sub39 n h) y hy0 hy1 hc C Z r hf
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
end
end N11Formalization.Paid16GeneralNext1182S05
#print axioms N11Formalization.Paid16GeneralNext1182S05.new_count
#print axioms N11Formalization.Paid16GeneralNext1182S05.new_radius
