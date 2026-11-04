import N11Formalization.EnergyTerminalResidualCensusBase

/-! Census part 04.  Every single source index has its own theorem so no
declaration carries more than one heavy `decide +kernel`; each block
lemma (`mem_iff_blockNN`) delegates to its 100 per-index lemmas via
explicit bullets.  The exported interface is unchanged.
-/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensus
open Finset
noncomputable section

theorem mem_iff_id_0300 (n : Fin 5011) (hn : n.val = 300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 300 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0301 (n : Fin 5011) (hn : n.val = 301) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 301 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0302 (n : Fin 5011) (hn : n.val = 302) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 302 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0303 (n : Fin 5011) (hn : n.val = 303) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 303 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0304 (n : Fin 5011) (hn : n.val = 304) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 304 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0305 (n : Fin 5011) (hn : n.val = 305) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 305 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0306 (n : Fin 5011) (hn : n.val = 306) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 306 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0307 (n : Fin 5011) (hn : n.val = 307) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 307 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0308 (n : Fin 5011) (hn : n.val = 308) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 308 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0309 (n : Fin 5011) (hn : n.val = 309) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 309 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0310 (n : Fin 5011) (hn : n.val = 310) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 310 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0311 (n : Fin 5011) (hn : n.val = 311) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 311 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0312 (n : Fin 5011) (hn : n.val = 312) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 312 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0313 (n : Fin 5011) (hn : n.val = 313) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 313 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0314 (n : Fin 5011) (hn : n.val = 314) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 314 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0315 (n : Fin 5011) (hn : n.val = 315) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 315 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0316 (n : Fin 5011) (hn : n.val = 316) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 316 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0317 (n : Fin 5011) (hn : n.val = 317) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 317 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0318 (n : Fin 5011) (hn : n.val = 318) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 318 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0319 (n : Fin 5011) (hn : n.val = 319) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 319 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0320 (n : Fin 5011) (hn : n.val = 320) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 320 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0321 (n : Fin 5011) (hn : n.val = 321) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 321 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0322 (n : Fin 5011) (hn : n.val = 322) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 322 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0323 (n : Fin 5011) (hn : n.val = 323) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 323 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0324 (n : Fin 5011) (hn : n.val = 324) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 324 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0325 (n : Fin 5011) (hn : n.val = 325) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 325 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0326 (n : Fin 5011) (hn : n.val = 326) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 326 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0327 (n : Fin 5011) (hn : n.val = 327) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 327 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0328 (n : Fin 5011) (hn : n.val = 328) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 328 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0329 (n : Fin 5011) (hn : n.val = 329) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 329 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0330 (n : Fin 5011) (hn : n.val = 330) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 330 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0331 (n : Fin 5011) (hn : n.val = 331) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 331 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0332 (n : Fin 5011) (hn : n.val = 332) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 332 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0333 (n : Fin 5011) (hn : n.val = 333) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 333 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0334 (n : Fin 5011) (hn : n.val = 334) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 334 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0335 (n : Fin 5011) (hn : n.val = 335) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 335 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0336 (n : Fin 5011) (hn : n.val = 336) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 336 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0337 (n : Fin 5011) (hn : n.val = 337) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 337 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0338 (n : Fin 5011) (hn : n.val = 338) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 338 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0339 (n : Fin 5011) (hn : n.val = 339) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 339 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0340 (n : Fin 5011) (hn : n.val = 340) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 340 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0341 (n : Fin 5011) (hn : n.val = 341) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 341 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0342 (n : Fin 5011) (hn : n.val = 342) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 342 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0343 (n : Fin 5011) (hn : n.val = 343) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 343 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0344 (n : Fin 5011) (hn : n.val = 344) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 344 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0345 (n : Fin 5011) (hn : n.val = 345) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 345 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0346 (n : Fin 5011) (hn : n.val = 346) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 346 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0347 (n : Fin 5011) (hn : n.val = 347) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 347 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0348 (n : Fin 5011) (hn : n.val = 348) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 348 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0349 (n : Fin 5011) (hn : n.val = 349) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 349 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0350 (n : Fin 5011) (hn : n.val = 350) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 350 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0351 (n : Fin 5011) (hn : n.val = 351) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 351 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0352 (n : Fin 5011) (hn : n.val = 352) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 352 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0353 (n : Fin 5011) (hn : n.val = 353) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 353 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0354 (n : Fin 5011) (hn : n.val = 354) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 354 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0355 (n : Fin 5011) (hn : n.val = 355) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 355 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0356 (n : Fin 5011) (hn : n.val = 356) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 356 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0357 (n : Fin 5011) (hn : n.val = 357) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 357 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0358 (n : Fin 5011) (hn : n.val = 358) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 358 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0359 (n : Fin 5011) (hn : n.val = 359) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 359 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0360 (n : Fin 5011) (hn : n.val = 360) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 360 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0361 (n : Fin 5011) (hn : n.val = 361) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 361 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0362 (n : Fin 5011) (hn : n.val = 362) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 362 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0363 (n : Fin 5011) (hn : n.val = 363) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 363 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0364 (n : Fin 5011) (hn : n.val = 364) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 364 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0365 (n : Fin 5011) (hn : n.val = 365) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 365 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0366 (n : Fin 5011) (hn : n.val = 366) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 366 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0367 (n : Fin 5011) (hn : n.val = 367) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 367 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0368 (n : Fin 5011) (hn : n.val = 368) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 368 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0369 (n : Fin 5011) (hn : n.val = 369) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 369 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0370 (n : Fin 5011) (hn : n.val = 370) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 370 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0371 (n : Fin 5011) (hn : n.val = 371) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 371 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0372 (n : Fin 5011) (hn : n.val = 372) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 372 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0373 (n : Fin 5011) (hn : n.val = 373) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 373 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0374 (n : Fin 5011) (hn : n.val = 374) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 374 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0375 (n : Fin 5011) (hn : n.val = 375) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 375 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0376 (n : Fin 5011) (hn : n.val = 376) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 376 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0377 (n : Fin 5011) (hn : n.val = 377) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 377 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0378 (n : Fin 5011) (hn : n.val = 378) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 378 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0379 (n : Fin 5011) (hn : n.val = 379) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 379 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0380 (n : Fin 5011) (hn : n.val = 380) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 380 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0381 (n : Fin 5011) (hn : n.val = 381) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 381 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0382 (n : Fin 5011) (hn : n.val = 382) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 382 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0383 (n : Fin 5011) (hn : n.val = 383) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 383 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0384 (n : Fin 5011) (hn : n.val = 384) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 384 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0385 (n : Fin 5011) (hn : n.val = 385) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 385 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0386 (n : Fin 5011) (hn : n.val = 386) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 386 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0387 (n : Fin 5011) (hn : n.val = 387) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 387 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0388 (n : Fin 5011) (hn : n.val = 388) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 388 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0389 (n : Fin 5011) (hn : n.val = 389) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 389 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0390 (n : Fin 5011) (hn : n.val = 390) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 390 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0391 (n : Fin 5011) (hn : n.val = 391) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 391 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0392 (n : Fin 5011) (hn : n.val = 392) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 392 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0393 (n : Fin 5011) (hn : n.val = 393) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 393 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0394 (n : Fin 5011) (hn : n.val = 394) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 394 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0395 (n : Fin 5011) (hn : n.val = 395) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 395 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0396 (n : Fin 5011) (hn : n.val = 396) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 396 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0397 (n : Fin 5011) (hn : n.val = 397) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 397 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0398 (n : Fin 5011) (hn : n.val = 398) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 398 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0399 (n : Fin 5011) (hn : n.val = 399) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 399 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0700 (n : Fin 5011) (hn : n.val = 700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 700 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0701 (n : Fin 5011) (hn : n.val = 701) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 701 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0702 (n : Fin 5011) (hn : n.val = 702) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 702 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0703 (n : Fin 5011) (hn : n.val = 703) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 703 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0704 (n : Fin 5011) (hn : n.val = 704) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 704 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0705 (n : Fin 5011) (hn : n.val = 705) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 705 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0706 (n : Fin 5011) (hn : n.val = 706) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 706 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0707 (n : Fin 5011) (hn : n.val = 707) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 707 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0708 (n : Fin 5011) (hn : n.val = 708) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 708 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0709 (n : Fin 5011) (hn : n.val = 709) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 709 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0710 (n : Fin 5011) (hn : n.val = 710) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 710 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0711 (n : Fin 5011) (hn : n.val = 711) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 711 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0712 (n : Fin 5011) (hn : n.val = 712) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 712 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0713 (n : Fin 5011) (hn : n.val = 713) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 713 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0714 (n : Fin 5011) (hn : n.val = 714) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 714 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0715 (n : Fin 5011) (hn : n.val = 715) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 715 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0716 (n : Fin 5011) (hn : n.val = 716) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 716 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0717 (n : Fin 5011) (hn : n.val = 717) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 717 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0718 (n : Fin 5011) (hn : n.val = 718) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 718 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0719 (n : Fin 5011) (hn : n.val = 719) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 719 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0720 (n : Fin 5011) (hn : n.val = 720) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 720 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0721 (n : Fin 5011) (hn : n.val = 721) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 721 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0722 (n : Fin 5011) (hn : n.val = 722) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 722 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0723 (n : Fin 5011) (hn : n.val = 723) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 723 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0724 (n : Fin 5011) (hn : n.val = 724) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 724 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0725 (n : Fin 5011) (hn : n.val = 725) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 725 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0726 (n : Fin 5011) (hn : n.val = 726) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 726 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0727 (n : Fin 5011) (hn : n.val = 727) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 727 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0728 (n : Fin 5011) (hn : n.val = 728) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 728 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0729 (n : Fin 5011) (hn : n.val = 729) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 729 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0730 (n : Fin 5011) (hn : n.val = 730) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 730 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0731 (n : Fin 5011) (hn : n.val = 731) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 731 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0732 (n : Fin 5011) (hn : n.val = 732) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 732 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0733 (n : Fin 5011) (hn : n.val = 733) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 733 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0734 (n : Fin 5011) (hn : n.val = 734) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 734 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0735 (n : Fin 5011) (hn : n.val = 735) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 735 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0736 (n : Fin 5011) (hn : n.val = 736) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 736 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0737 (n : Fin 5011) (hn : n.val = 737) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 737 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0738 (n : Fin 5011) (hn : n.val = 738) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 738 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0739 (n : Fin 5011) (hn : n.val = 739) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 739 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0740 (n : Fin 5011) (hn : n.val = 740) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 740 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0741 (n : Fin 5011) (hn : n.val = 741) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 741 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0742 (n : Fin 5011) (hn : n.val = 742) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 742 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0743 (n : Fin 5011) (hn : n.val = 743) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 743 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0744 (n : Fin 5011) (hn : n.val = 744) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 744 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0745 (n : Fin 5011) (hn : n.val = 745) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 745 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0746 (n : Fin 5011) (hn : n.val = 746) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 746 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0747 (n : Fin 5011) (hn : n.val = 747) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 747 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0748 (n : Fin 5011) (hn : n.val = 748) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 748 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0749 (n : Fin 5011) (hn : n.val = 749) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 749 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0750 (n : Fin 5011) (hn : n.val = 750) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 750 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0751 (n : Fin 5011) (hn : n.val = 751) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 751 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0752 (n : Fin 5011) (hn : n.val = 752) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 752 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0753 (n : Fin 5011) (hn : n.val = 753) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 753 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0754 (n : Fin 5011) (hn : n.val = 754) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 754 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0755 (n : Fin 5011) (hn : n.val = 755) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 755 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0756 (n : Fin 5011) (hn : n.val = 756) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 756 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0757 (n : Fin 5011) (hn : n.val = 757) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 757 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0758 (n : Fin 5011) (hn : n.val = 758) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 758 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0759 (n : Fin 5011) (hn : n.val = 759) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 759 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0760 (n : Fin 5011) (hn : n.val = 760) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 760 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0761 (n : Fin 5011) (hn : n.val = 761) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 761 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0762 (n : Fin 5011) (hn : n.val = 762) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 762 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0763 (n : Fin 5011) (hn : n.val = 763) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 763 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0764 (n : Fin 5011) (hn : n.val = 764) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 764 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0765 (n : Fin 5011) (hn : n.val = 765) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 765 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0766 (n : Fin 5011) (hn : n.val = 766) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 766 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0767 (n : Fin 5011) (hn : n.val = 767) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 767 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0768 (n : Fin 5011) (hn : n.val = 768) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 768 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0769 (n : Fin 5011) (hn : n.val = 769) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 769 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0770 (n : Fin 5011) (hn : n.val = 770) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 770 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0771 (n : Fin 5011) (hn : n.val = 771) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 771 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0772 (n : Fin 5011) (hn : n.val = 772) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 772 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0773 (n : Fin 5011) (hn : n.val = 773) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 773 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0774 (n : Fin 5011) (hn : n.val = 774) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 774 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0775 (n : Fin 5011) (hn : n.val = 775) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 775 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0776 (n : Fin 5011) (hn : n.val = 776) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 776 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0777 (n : Fin 5011) (hn : n.val = 777) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 777 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0778 (n : Fin 5011) (hn : n.val = 778) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 778 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0779 (n : Fin 5011) (hn : n.val = 779) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 779 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0780 (n : Fin 5011) (hn : n.val = 780) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 780 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0781 (n : Fin 5011) (hn : n.val = 781) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 781 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0782 (n : Fin 5011) (hn : n.val = 782) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 782 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0783 (n : Fin 5011) (hn : n.val = 783) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 783 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0784 (n : Fin 5011) (hn : n.val = 784) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 784 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0785 (n : Fin 5011) (hn : n.val = 785) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 785 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0786 (n : Fin 5011) (hn : n.val = 786) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 786 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0787 (n : Fin 5011) (hn : n.val = 787) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 787 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0788 (n : Fin 5011) (hn : n.val = 788) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 788 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0789 (n : Fin 5011) (hn : n.val = 789) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 789 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0790 (n : Fin 5011) (hn : n.val = 790) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 790 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0791 (n : Fin 5011) (hn : n.val = 791) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 791 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0792 (n : Fin 5011) (hn : n.val = 792) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 792 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0793 (n : Fin 5011) (hn : n.val = 793) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 793 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0794 (n : Fin 5011) (hn : n.val = 794) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 794 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0795 (n : Fin 5011) (hn : n.val = 795) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 795 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0796 (n : Fin 5011) (hn : n.val = 796) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 796 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0797 (n : Fin 5011) (hn : n.val = 797) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 797 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0798 (n : Fin 5011) (hn : n.val = 798) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 798 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0799 (n : Fin 5011) (hn : n.val = 799) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 799 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1100 (n : Fin 5011) (hn : n.val = 1100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1100 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1101 (n : Fin 5011) (hn : n.val = 1101) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1101 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1102 (n : Fin 5011) (hn : n.val = 1102) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1102 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1103 (n : Fin 5011) (hn : n.val = 1103) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1103 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1104 (n : Fin 5011) (hn : n.val = 1104) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1104 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1105 (n : Fin 5011) (hn : n.val = 1105) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1105 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1106 (n : Fin 5011) (hn : n.val = 1106) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1106 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1107 (n : Fin 5011) (hn : n.val = 1107) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1107 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1108 (n : Fin 5011) (hn : n.val = 1108) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1108 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1109 (n : Fin 5011) (hn : n.val = 1109) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1109 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1110 (n : Fin 5011) (hn : n.val = 1110) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1110 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1111 (n : Fin 5011) (hn : n.val = 1111) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1111 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1112 (n : Fin 5011) (hn : n.val = 1112) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1112 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1113 (n : Fin 5011) (hn : n.val = 1113) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1113 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1114 (n : Fin 5011) (hn : n.val = 1114) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1114 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1115 (n : Fin 5011) (hn : n.val = 1115) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1115 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1116 (n : Fin 5011) (hn : n.val = 1116) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1116 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1117 (n : Fin 5011) (hn : n.val = 1117) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1117 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1118 (n : Fin 5011) (hn : n.val = 1118) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1118 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1119 (n : Fin 5011) (hn : n.val = 1119) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1119 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1120 (n : Fin 5011) (hn : n.val = 1120) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1120 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1121 (n : Fin 5011) (hn : n.val = 1121) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1121 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1122 (n : Fin 5011) (hn : n.val = 1122) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1122 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1123 (n : Fin 5011) (hn : n.val = 1123) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1123 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1124 (n : Fin 5011) (hn : n.val = 1124) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1124 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1125 (n : Fin 5011) (hn : n.val = 1125) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1125 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1126 (n : Fin 5011) (hn : n.val = 1126) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1126 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1127 (n : Fin 5011) (hn : n.val = 1127) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1127 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1128 (n : Fin 5011) (hn : n.val = 1128) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1128 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1129 (n : Fin 5011) (hn : n.val = 1129) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1129 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1130 (n : Fin 5011) (hn : n.val = 1130) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1130 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1131 (n : Fin 5011) (hn : n.val = 1131) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1131 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1132 (n : Fin 5011) (hn : n.val = 1132) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1132 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1133 (n : Fin 5011) (hn : n.val = 1133) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1133 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1134 (n : Fin 5011) (hn : n.val = 1134) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1134 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1135 (n : Fin 5011) (hn : n.val = 1135) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1135 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1136 (n : Fin 5011) (hn : n.val = 1136) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1136 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1137 (n : Fin 5011) (hn : n.val = 1137) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1137 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1138 (n : Fin 5011) (hn : n.val = 1138) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1138 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1139 (n : Fin 5011) (hn : n.val = 1139) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1139 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1140 (n : Fin 5011) (hn : n.val = 1140) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1140 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1141 (n : Fin 5011) (hn : n.val = 1141) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1141 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1142 (n : Fin 5011) (hn : n.val = 1142) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1142 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1143 (n : Fin 5011) (hn : n.val = 1143) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1143 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1144 (n : Fin 5011) (hn : n.val = 1144) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1144 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1145 (n : Fin 5011) (hn : n.val = 1145) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1145 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1146 (n : Fin 5011) (hn : n.val = 1146) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1146 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1147 (n : Fin 5011) (hn : n.val = 1147) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1147 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1148 (n : Fin 5011) (hn : n.val = 1148) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1148 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1149 (n : Fin 5011) (hn : n.val = 1149) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1149 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1150 (n : Fin 5011) (hn : n.val = 1150) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1150 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1151 (n : Fin 5011) (hn : n.val = 1151) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1151 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1152 (n : Fin 5011) (hn : n.val = 1152) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1152 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1153 (n : Fin 5011) (hn : n.val = 1153) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1153 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1154 (n : Fin 5011) (hn : n.val = 1154) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1154 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1155 (n : Fin 5011) (hn : n.val = 1155) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1155 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1156 (n : Fin 5011) (hn : n.val = 1156) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1156 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1157 (n : Fin 5011) (hn : n.val = 1157) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1157 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1158 (n : Fin 5011) (hn : n.val = 1158) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1158 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1159 (n : Fin 5011) (hn : n.val = 1159) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1159 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1160 (n : Fin 5011) (hn : n.val = 1160) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1160 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1161 (n : Fin 5011) (hn : n.val = 1161) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1161 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1162 (n : Fin 5011) (hn : n.val = 1162) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1162 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1163 (n : Fin 5011) (hn : n.val = 1163) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1163 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1164 (n : Fin 5011) (hn : n.val = 1164) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1164 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1165 (n : Fin 5011) (hn : n.val = 1165) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1165 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1166 (n : Fin 5011) (hn : n.val = 1166) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1166 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1167 (n : Fin 5011) (hn : n.val = 1167) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1167 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1168 (n : Fin 5011) (hn : n.val = 1168) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1168 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1169 (n : Fin 5011) (hn : n.val = 1169) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1169 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1170 (n : Fin 5011) (hn : n.val = 1170) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1170 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1171 (n : Fin 5011) (hn : n.val = 1171) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1171 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1172 (n : Fin 5011) (hn : n.val = 1172) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1172 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1173 (n : Fin 5011) (hn : n.val = 1173) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1173 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1174 (n : Fin 5011) (hn : n.val = 1174) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1174 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1175 (n : Fin 5011) (hn : n.val = 1175) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1175 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1176 (n : Fin 5011) (hn : n.val = 1176) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1176 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1177 (n : Fin 5011) (hn : n.val = 1177) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1177 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1178 (n : Fin 5011) (hn : n.val = 1178) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1178 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1179 (n : Fin 5011) (hn : n.val = 1179) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1179 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1180 (n : Fin 5011) (hn : n.val = 1180) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1180 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1181 (n : Fin 5011) (hn : n.val = 1181) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1181 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1182 (n : Fin 5011) (hn : n.val = 1182) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1182 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1183 (n : Fin 5011) (hn : n.val = 1183) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1183 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1184 (n : Fin 5011) (hn : n.val = 1184) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1184 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1185 (n : Fin 5011) (hn : n.val = 1185) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1185 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1186 (n : Fin 5011) (hn : n.val = 1186) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1186 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1187 (n : Fin 5011) (hn : n.val = 1187) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1187 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1188 (n : Fin 5011) (hn : n.val = 1188) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1188 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1189 (n : Fin 5011) (hn : n.val = 1189) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1189 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1190 (n : Fin 5011) (hn : n.val = 1190) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1190 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1191 (n : Fin 5011) (hn : n.val = 1191) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1191 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1192 (n : Fin 5011) (hn : n.val = 1192) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1192 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1193 (n : Fin 5011) (hn : n.val = 1193) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1193 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1194 (n : Fin 5011) (hn : n.val = 1194) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1194 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1195 (n : Fin 5011) (hn : n.val = 1195) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1195 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1196 (n : Fin 5011) (hn : n.val = 1196) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1196 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1197 (n : Fin 5011) (hn : n.val = 1197) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1197 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1198 (n : Fin 5011) (hn : n.val = 1198) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1198 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1199 (n : Fin 5011) (hn : n.val = 1199) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1199 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1500 (n : Fin 5011) (hn : n.val = 1500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1500 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1501 (n : Fin 5011) (hn : n.val = 1501) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1501 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1502 (n : Fin 5011) (hn : n.val = 1502) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1502 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1503 (n : Fin 5011) (hn : n.val = 1503) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1503 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1504 (n : Fin 5011) (hn : n.val = 1504) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1504 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1505 (n : Fin 5011) (hn : n.val = 1505) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1505 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1506 (n : Fin 5011) (hn : n.val = 1506) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1506 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1507 (n : Fin 5011) (hn : n.val = 1507) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1507 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1508 (n : Fin 5011) (hn : n.val = 1508) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1508 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1509 (n : Fin 5011) (hn : n.val = 1509) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1509 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1510 (n : Fin 5011) (hn : n.val = 1510) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1510 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1511 (n : Fin 5011) (hn : n.val = 1511) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1511 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1512 (n : Fin 5011) (hn : n.val = 1512) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1512 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1513 (n : Fin 5011) (hn : n.val = 1513) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1513 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1514 (n : Fin 5011) (hn : n.val = 1514) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1514 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1515 (n : Fin 5011) (hn : n.val = 1515) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1515 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1516 (n : Fin 5011) (hn : n.val = 1516) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1516 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1517 (n : Fin 5011) (hn : n.val = 1517) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1517 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1518 (n : Fin 5011) (hn : n.val = 1518) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1518 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1519 (n : Fin 5011) (hn : n.val = 1519) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1519 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1520 (n : Fin 5011) (hn : n.val = 1520) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1520 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1521 (n : Fin 5011) (hn : n.val = 1521) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1521 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1522 (n : Fin 5011) (hn : n.val = 1522) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1522 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1523 (n : Fin 5011) (hn : n.val = 1523) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1523 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1524 (n : Fin 5011) (hn : n.val = 1524) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1524 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1525 (n : Fin 5011) (hn : n.val = 1525) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1525 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1526 (n : Fin 5011) (hn : n.val = 1526) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1526 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1527 (n : Fin 5011) (hn : n.val = 1527) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1527 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1528 (n : Fin 5011) (hn : n.val = 1528) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1528 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1529 (n : Fin 5011) (hn : n.val = 1529) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1529 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1530 (n : Fin 5011) (hn : n.val = 1530) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1530 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1531 (n : Fin 5011) (hn : n.val = 1531) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1531 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1532 (n : Fin 5011) (hn : n.val = 1532) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1532 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1533 (n : Fin 5011) (hn : n.val = 1533) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1533 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1534 (n : Fin 5011) (hn : n.val = 1534) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1534 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1535 (n : Fin 5011) (hn : n.val = 1535) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1535 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1536 (n : Fin 5011) (hn : n.val = 1536) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1536 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1537 (n : Fin 5011) (hn : n.val = 1537) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1537 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1538 (n : Fin 5011) (hn : n.val = 1538) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1538 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1539 (n : Fin 5011) (hn : n.val = 1539) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1539 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1540 (n : Fin 5011) (hn : n.val = 1540) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1540 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1541 (n : Fin 5011) (hn : n.val = 1541) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1541 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1542 (n : Fin 5011) (hn : n.val = 1542) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1542 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1543 (n : Fin 5011) (hn : n.val = 1543) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1543 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1544 (n : Fin 5011) (hn : n.val = 1544) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1544 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1545 (n : Fin 5011) (hn : n.val = 1545) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1545 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1546 (n : Fin 5011) (hn : n.val = 1546) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1546 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1547 (n : Fin 5011) (hn : n.val = 1547) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1547 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1548 (n : Fin 5011) (hn : n.val = 1548) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1548 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1549 (n : Fin 5011) (hn : n.val = 1549) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1549 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1550 (n : Fin 5011) (hn : n.val = 1550) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1550 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1551 (n : Fin 5011) (hn : n.val = 1551) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1551 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1552 (n : Fin 5011) (hn : n.val = 1552) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1552 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1553 (n : Fin 5011) (hn : n.val = 1553) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1553 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1554 (n : Fin 5011) (hn : n.val = 1554) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1554 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1555 (n : Fin 5011) (hn : n.val = 1555) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1555 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1556 (n : Fin 5011) (hn : n.val = 1556) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1556 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1557 (n : Fin 5011) (hn : n.val = 1557) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1557 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1558 (n : Fin 5011) (hn : n.val = 1558) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1558 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1559 (n : Fin 5011) (hn : n.val = 1559) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1559 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1560 (n : Fin 5011) (hn : n.val = 1560) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1560 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1561 (n : Fin 5011) (hn : n.val = 1561) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1561 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1562 (n : Fin 5011) (hn : n.val = 1562) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1562 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1563 (n : Fin 5011) (hn : n.val = 1563) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1563 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1564 (n : Fin 5011) (hn : n.val = 1564) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1564 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1565 (n : Fin 5011) (hn : n.val = 1565) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1565 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1566 (n : Fin 5011) (hn : n.val = 1566) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1566 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1567 (n : Fin 5011) (hn : n.val = 1567) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1567 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1568 (n : Fin 5011) (hn : n.val = 1568) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1568 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1569 (n : Fin 5011) (hn : n.val = 1569) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1569 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1570 (n : Fin 5011) (hn : n.val = 1570) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1570 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1571 (n : Fin 5011) (hn : n.val = 1571) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1571 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1572 (n : Fin 5011) (hn : n.val = 1572) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1572 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1573 (n : Fin 5011) (hn : n.val = 1573) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1573 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1574 (n : Fin 5011) (hn : n.val = 1574) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1574 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1575 (n : Fin 5011) (hn : n.val = 1575) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1575 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1576 (n : Fin 5011) (hn : n.val = 1576) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1576 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1577 (n : Fin 5011) (hn : n.val = 1577) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1577 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1578 (n : Fin 5011) (hn : n.val = 1578) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1578 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1579 (n : Fin 5011) (hn : n.val = 1579) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1579 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1580 (n : Fin 5011) (hn : n.val = 1580) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1580 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1581 (n : Fin 5011) (hn : n.val = 1581) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1581 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1582 (n : Fin 5011) (hn : n.val = 1582) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1582 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1583 (n : Fin 5011) (hn : n.val = 1583) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1583 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1584 (n : Fin 5011) (hn : n.val = 1584) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1584 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1585 (n : Fin 5011) (hn : n.val = 1585) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1585 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1586 (n : Fin 5011) (hn : n.val = 1586) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1586 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1587 (n : Fin 5011) (hn : n.val = 1587) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1587 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1588 (n : Fin 5011) (hn : n.val = 1588) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1588 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1589 (n : Fin 5011) (hn : n.val = 1589) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1589 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1590 (n : Fin 5011) (hn : n.val = 1590) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1590 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1591 (n : Fin 5011) (hn : n.val = 1591) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1591 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1592 (n : Fin 5011) (hn : n.val = 1592) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1592 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1593 (n : Fin 5011) (hn : n.val = 1593) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1593 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1594 (n : Fin 5011) (hn : n.val = 1594) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1594 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1595 (n : Fin 5011) (hn : n.val = 1595) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1595 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1596 (n : Fin 5011) (hn : n.val = 1596) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1596 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1597 (n : Fin 5011) (hn : n.val = 1597) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1597 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1598 (n : Fin 5011) (hn : n.val = 1598) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1598 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1599 (n : Fin 5011) (hn : n.val = 1599) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1599 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1900 (n : Fin 5011) (hn : n.val = 1900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1900 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1901 (n : Fin 5011) (hn : n.val = 1901) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1901 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1902 (n : Fin 5011) (hn : n.val = 1902) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1902 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1903 (n : Fin 5011) (hn : n.val = 1903) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1903 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1904 (n : Fin 5011) (hn : n.val = 1904) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1904 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1905 (n : Fin 5011) (hn : n.val = 1905) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1905 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1906 (n : Fin 5011) (hn : n.val = 1906) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1906 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1907 (n : Fin 5011) (hn : n.val = 1907) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1907 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1908 (n : Fin 5011) (hn : n.val = 1908) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1908 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1909 (n : Fin 5011) (hn : n.val = 1909) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1909 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1910 (n : Fin 5011) (hn : n.val = 1910) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1910 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1911 (n : Fin 5011) (hn : n.val = 1911) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1911 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1912 (n : Fin 5011) (hn : n.val = 1912) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1912 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1913 (n : Fin 5011) (hn : n.val = 1913) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1913 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1914 (n : Fin 5011) (hn : n.val = 1914) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1914 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1915 (n : Fin 5011) (hn : n.val = 1915) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1915 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1916 (n : Fin 5011) (hn : n.val = 1916) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1916 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1917 (n : Fin 5011) (hn : n.val = 1917) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1917 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1918 (n : Fin 5011) (hn : n.val = 1918) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1918 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1919 (n : Fin 5011) (hn : n.val = 1919) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1919 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1920 (n : Fin 5011) (hn : n.val = 1920) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1920 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1921 (n : Fin 5011) (hn : n.val = 1921) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1921 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1922 (n : Fin 5011) (hn : n.val = 1922) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1922 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1923 (n : Fin 5011) (hn : n.val = 1923) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1923 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1924 (n : Fin 5011) (hn : n.val = 1924) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1924 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1925 (n : Fin 5011) (hn : n.val = 1925) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1925 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1926 (n : Fin 5011) (hn : n.val = 1926) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1926 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1927 (n : Fin 5011) (hn : n.val = 1927) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1927 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1928 (n : Fin 5011) (hn : n.val = 1928) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1928 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1929 (n : Fin 5011) (hn : n.val = 1929) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1929 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1930 (n : Fin 5011) (hn : n.val = 1930) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1930 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1931 (n : Fin 5011) (hn : n.val = 1931) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1931 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1932 (n : Fin 5011) (hn : n.val = 1932) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1932 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1933 (n : Fin 5011) (hn : n.val = 1933) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1933 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1934 (n : Fin 5011) (hn : n.val = 1934) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1934 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1935 (n : Fin 5011) (hn : n.val = 1935) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1935 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1936 (n : Fin 5011) (hn : n.val = 1936) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1936 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1937 (n : Fin 5011) (hn : n.val = 1937) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1937 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1938 (n : Fin 5011) (hn : n.val = 1938) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1938 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1939 (n : Fin 5011) (hn : n.val = 1939) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1939 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1940 (n : Fin 5011) (hn : n.val = 1940) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1940 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1941 (n : Fin 5011) (hn : n.val = 1941) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1941 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1942 (n : Fin 5011) (hn : n.val = 1942) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1942 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1943 (n : Fin 5011) (hn : n.val = 1943) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1943 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1944 (n : Fin 5011) (hn : n.val = 1944) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1944 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1945 (n : Fin 5011) (hn : n.val = 1945) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1945 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1946 (n : Fin 5011) (hn : n.val = 1946) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1946 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1947 (n : Fin 5011) (hn : n.val = 1947) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1947 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1948 (n : Fin 5011) (hn : n.val = 1948) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1948 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1949 (n : Fin 5011) (hn : n.val = 1949) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1949 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1950 (n : Fin 5011) (hn : n.val = 1950) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1950 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1951 (n : Fin 5011) (hn : n.val = 1951) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1951 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1952 (n : Fin 5011) (hn : n.val = 1952) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1952 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1953 (n : Fin 5011) (hn : n.val = 1953) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1953 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1954 (n : Fin 5011) (hn : n.val = 1954) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1954 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1955 (n : Fin 5011) (hn : n.val = 1955) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1955 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1956 (n : Fin 5011) (hn : n.val = 1956) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1956 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1957 (n : Fin 5011) (hn : n.val = 1957) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1957 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1958 (n : Fin 5011) (hn : n.val = 1958) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1958 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1959 (n : Fin 5011) (hn : n.val = 1959) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1959 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1960 (n : Fin 5011) (hn : n.val = 1960) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1960 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1961 (n : Fin 5011) (hn : n.val = 1961) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1961 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1962 (n : Fin 5011) (hn : n.val = 1962) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1962 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1963 (n : Fin 5011) (hn : n.val = 1963) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1963 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1964 (n : Fin 5011) (hn : n.val = 1964) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1964 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1965 (n : Fin 5011) (hn : n.val = 1965) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1965 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1966 (n : Fin 5011) (hn : n.val = 1966) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1966 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1967 (n : Fin 5011) (hn : n.val = 1967) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1967 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1968 (n : Fin 5011) (hn : n.val = 1968) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1968 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1969 (n : Fin 5011) (hn : n.val = 1969) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1969 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1970 (n : Fin 5011) (hn : n.val = 1970) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1970 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1971 (n : Fin 5011) (hn : n.val = 1971) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1971 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1972 (n : Fin 5011) (hn : n.val = 1972) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1972 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1973 (n : Fin 5011) (hn : n.val = 1973) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1973 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1974 (n : Fin 5011) (hn : n.val = 1974) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1974 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1975 (n : Fin 5011) (hn : n.val = 1975) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1975 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1976 (n : Fin 5011) (hn : n.val = 1976) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1976 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1977 (n : Fin 5011) (hn : n.val = 1977) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1977 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1978 (n : Fin 5011) (hn : n.val = 1978) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1978 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1979 (n : Fin 5011) (hn : n.val = 1979) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1979 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1980 (n : Fin 5011) (hn : n.val = 1980) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1980 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1981 (n : Fin 5011) (hn : n.val = 1981) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1981 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1982 (n : Fin 5011) (hn : n.val = 1982) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1982 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1983 (n : Fin 5011) (hn : n.val = 1983) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1983 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1984 (n : Fin 5011) (hn : n.val = 1984) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1984 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1985 (n : Fin 5011) (hn : n.val = 1985) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1985 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1986 (n : Fin 5011) (hn : n.val = 1986) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1986 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1987 (n : Fin 5011) (hn : n.val = 1987) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1987 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1988 (n : Fin 5011) (hn : n.val = 1988) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1988 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1989 (n : Fin 5011) (hn : n.val = 1989) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1989 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1990 (n : Fin 5011) (hn : n.val = 1990) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1990 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1991 (n : Fin 5011) (hn : n.val = 1991) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1991 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1992 (n : Fin 5011) (hn : n.val = 1992) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1992 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1993 (n : Fin 5011) (hn : n.val = 1993) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1993 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1994 (n : Fin 5011) (hn : n.val = 1994) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1994 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1995 (n : Fin 5011) (hn : n.val = 1995) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1995 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1996 (n : Fin 5011) (hn : n.val = 1996) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1996 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1997 (n : Fin 5011) (hn : n.val = 1997) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1997 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1998 (n : Fin 5011) (hn : n.val = 1998) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1998 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1999 (n : Fin 5011) (hn : n.val = 1999) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1999 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2300 (n : Fin 5011) (hn : n.val = 2300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2300 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2301 (n : Fin 5011) (hn : n.val = 2301) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2301 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2302 (n : Fin 5011) (hn : n.val = 2302) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2302 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2303 (n : Fin 5011) (hn : n.val = 2303) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2303 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2304 (n : Fin 5011) (hn : n.val = 2304) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2304 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2305 (n : Fin 5011) (hn : n.val = 2305) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2305 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2306 (n : Fin 5011) (hn : n.val = 2306) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2306 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2307 (n : Fin 5011) (hn : n.val = 2307) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2307 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2308 (n : Fin 5011) (hn : n.val = 2308) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2308 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2309 (n : Fin 5011) (hn : n.val = 2309) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2309 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2310 (n : Fin 5011) (hn : n.val = 2310) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2310 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2311 (n : Fin 5011) (hn : n.val = 2311) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2311 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2312 (n : Fin 5011) (hn : n.val = 2312) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2312 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2313 (n : Fin 5011) (hn : n.val = 2313) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2313 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2314 (n : Fin 5011) (hn : n.val = 2314) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2314 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2315 (n : Fin 5011) (hn : n.val = 2315) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2315 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2316 (n : Fin 5011) (hn : n.val = 2316) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2316 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2317 (n : Fin 5011) (hn : n.val = 2317) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2317 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2318 (n : Fin 5011) (hn : n.val = 2318) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2318 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2319 (n : Fin 5011) (hn : n.val = 2319) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2319 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2320 (n : Fin 5011) (hn : n.val = 2320) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2320 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2321 (n : Fin 5011) (hn : n.val = 2321) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2321 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2322 (n : Fin 5011) (hn : n.val = 2322) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2322 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2323 (n : Fin 5011) (hn : n.val = 2323) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2323 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2324 (n : Fin 5011) (hn : n.val = 2324) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2324 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2325 (n : Fin 5011) (hn : n.val = 2325) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2325 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2326 (n : Fin 5011) (hn : n.val = 2326) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2326 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2327 (n : Fin 5011) (hn : n.val = 2327) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2327 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2328 (n : Fin 5011) (hn : n.val = 2328) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2328 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2329 (n : Fin 5011) (hn : n.val = 2329) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2329 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2330 (n : Fin 5011) (hn : n.val = 2330) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2330 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2331 (n : Fin 5011) (hn : n.val = 2331) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2331 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2332 (n : Fin 5011) (hn : n.val = 2332) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2332 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2333 (n : Fin 5011) (hn : n.val = 2333) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2333 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2334 (n : Fin 5011) (hn : n.val = 2334) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2334 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2335 (n : Fin 5011) (hn : n.val = 2335) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2335 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2336 (n : Fin 5011) (hn : n.val = 2336) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2336 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2337 (n : Fin 5011) (hn : n.val = 2337) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2337 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2338 (n : Fin 5011) (hn : n.val = 2338) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2338 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2339 (n : Fin 5011) (hn : n.val = 2339) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2339 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2340 (n : Fin 5011) (hn : n.val = 2340) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2340 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2341 (n : Fin 5011) (hn : n.val = 2341) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2341 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2342 (n : Fin 5011) (hn : n.val = 2342) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2342 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2343 (n : Fin 5011) (hn : n.val = 2343) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2343 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2344 (n : Fin 5011) (hn : n.val = 2344) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2344 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2345 (n : Fin 5011) (hn : n.val = 2345) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2345 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2346 (n : Fin 5011) (hn : n.val = 2346) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2346 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2347 (n : Fin 5011) (hn : n.val = 2347) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2347 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2348 (n : Fin 5011) (hn : n.val = 2348) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2348 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2349 (n : Fin 5011) (hn : n.val = 2349) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2349 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2350 (n : Fin 5011) (hn : n.val = 2350) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2350 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2351 (n : Fin 5011) (hn : n.val = 2351) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2351 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2352 (n : Fin 5011) (hn : n.val = 2352) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2352 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2353 (n : Fin 5011) (hn : n.val = 2353) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2353 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2354 (n : Fin 5011) (hn : n.val = 2354) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2354 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2355 (n : Fin 5011) (hn : n.val = 2355) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2355 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2356 (n : Fin 5011) (hn : n.val = 2356) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2356 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2357 (n : Fin 5011) (hn : n.val = 2357) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2357 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2358 (n : Fin 5011) (hn : n.val = 2358) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2358 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2359 (n : Fin 5011) (hn : n.val = 2359) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2359 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2360 (n : Fin 5011) (hn : n.val = 2360) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2360 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2361 (n : Fin 5011) (hn : n.val = 2361) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2361 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2362 (n : Fin 5011) (hn : n.val = 2362) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2362 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2363 (n : Fin 5011) (hn : n.val = 2363) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2363 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2364 (n : Fin 5011) (hn : n.val = 2364) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2364 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2365 (n : Fin 5011) (hn : n.val = 2365) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2365 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2366 (n : Fin 5011) (hn : n.val = 2366) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2366 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2367 (n : Fin 5011) (hn : n.val = 2367) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2367 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2368 (n : Fin 5011) (hn : n.val = 2368) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2368 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2369 (n : Fin 5011) (hn : n.val = 2369) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2369 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2370 (n : Fin 5011) (hn : n.val = 2370) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2370 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2371 (n : Fin 5011) (hn : n.val = 2371) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2371 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2372 (n : Fin 5011) (hn : n.val = 2372) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2372 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2373 (n : Fin 5011) (hn : n.val = 2373) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2373 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2374 (n : Fin 5011) (hn : n.val = 2374) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2374 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2375 (n : Fin 5011) (hn : n.val = 2375) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2375 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2376 (n : Fin 5011) (hn : n.val = 2376) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2376 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2377 (n : Fin 5011) (hn : n.val = 2377) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2377 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2378 (n : Fin 5011) (hn : n.val = 2378) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2378 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2379 (n : Fin 5011) (hn : n.val = 2379) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2379 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2380 (n : Fin 5011) (hn : n.val = 2380) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2380 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2381 (n : Fin 5011) (hn : n.val = 2381) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2381 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2382 (n : Fin 5011) (hn : n.val = 2382) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2382 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2383 (n : Fin 5011) (hn : n.val = 2383) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2383 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2384 (n : Fin 5011) (hn : n.val = 2384) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2384 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2385 (n : Fin 5011) (hn : n.val = 2385) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2385 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2386 (n : Fin 5011) (hn : n.val = 2386) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2386 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2387 (n : Fin 5011) (hn : n.val = 2387) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2387 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2388 (n : Fin 5011) (hn : n.val = 2388) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2388 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2389 (n : Fin 5011) (hn : n.val = 2389) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2389 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2390 (n : Fin 5011) (hn : n.val = 2390) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2390 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2391 (n : Fin 5011) (hn : n.val = 2391) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2391 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2392 (n : Fin 5011) (hn : n.val = 2392) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2392 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2393 (n : Fin 5011) (hn : n.val = 2393) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2393 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2394 (n : Fin 5011) (hn : n.val = 2394) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2394 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2395 (n : Fin 5011) (hn : n.val = 2395) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2395 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2396 (n : Fin 5011) (hn : n.val = 2396) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2396 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2397 (n : Fin 5011) (hn : n.val = 2397) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2397 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2398 (n : Fin 5011) (hn : n.val = 2398) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2398 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2399 (n : Fin 5011) (hn : n.val = 2399) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2399 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2700 (n : Fin 5011) (hn : n.val = 2700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2700 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2701 (n : Fin 5011) (hn : n.val = 2701) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2701 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2702 (n : Fin 5011) (hn : n.val = 2702) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2702 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2703 (n : Fin 5011) (hn : n.val = 2703) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2703 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2704 (n : Fin 5011) (hn : n.val = 2704) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2704 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2705 (n : Fin 5011) (hn : n.val = 2705) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2705 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2706 (n : Fin 5011) (hn : n.val = 2706) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2706 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2707 (n : Fin 5011) (hn : n.val = 2707) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2707 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2708 (n : Fin 5011) (hn : n.val = 2708) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2708 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2709 (n : Fin 5011) (hn : n.val = 2709) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2709 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2710 (n : Fin 5011) (hn : n.val = 2710) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2710 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2711 (n : Fin 5011) (hn : n.val = 2711) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2711 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2712 (n : Fin 5011) (hn : n.val = 2712) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2712 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2713 (n : Fin 5011) (hn : n.val = 2713) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2713 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2714 (n : Fin 5011) (hn : n.val = 2714) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2714 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2715 (n : Fin 5011) (hn : n.val = 2715) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2715 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2716 (n : Fin 5011) (hn : n.val = 2716) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2716 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2717 (n : Fin 5011) (hn : n.val = 2717) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2717 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2718 (n : Fin 5011) (hn : n.val = 2718) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2718 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2719 (n : Fin 5011) (hn : n.val = 2719) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2719 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2720 (n : Fin 5011) (hn : n.val = 2720) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2720 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2721 (n : Fin 5011) (hn : n.val = 2721) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2721 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2722 (n : Fin 5011) (hn : n.val = 2722) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2722 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2723 (n : Fin 5011) (hn : n.val = 2723) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2723 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2724 (n : Fin 5011) (hn : n.val = 2724) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2724 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2725 (n : Fin 5011) (hn : n.val = 2725) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2725 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2726 (n : Fin 5011) (hn : n.val = 2726) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2726 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2727 (n : Fin 5011) (hn : n.val = 2727) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2727 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2728 (n : Fin 5011) (hn : n.val = 2728) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2728 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2729 (n : Fin 5011) (hn : n.val = 2729) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2729 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2730 (n : Fin 5011) (hn : n.val = 2730) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2730 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2731 (n : Fin 5011) (hn : n.val = 2731) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2731 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2732 (n : Fin 5011) (hn : n.val = 2732) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2732 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2733 (n : Fin 5011) (hn : n.val = 2733) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2733 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2734 (n : Fin 5011) (hn : n.val = 2734) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2734 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2735 (n : Fin 5011) (hn : n.val = 2735) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2735 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2736 (n : Fin 5011) (hn : n.val = 2736) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2736 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2737 (n : Fin 5011) (hn : n.val = 2737) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2737 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2738 (n : Fin 5011) (hn : n.val = 2738) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2738 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2739 (n : Fin 5011) (hn : n.val = 2739) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2739 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2740 (n : Fin 5011) (hn : n.val = 2740) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2740 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2741 (n : Fin 5011) (hn : n.val = 2741) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2741 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2742 (n : Fin 5011) (hn : n.val = 2742) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2742 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2743 (n : Fin 5011) (hn : n.val = 2743) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2743 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2744 (n : Fin 5011) (hn : n.val = 2744) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2744 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2745 (n : Fin 5011) (hn : n.val = 2745) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2745 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2746 (n : Fin 5011) (hn : n.val = 2746) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2746 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2747 (n : Fin 5011) (hn : n.val = 2747) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2747 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2748 (n : Fin 5011) (hn : n.val = 2748) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2748 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2749 (n : Fin 5011) (hn : n.val = 2749) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2749 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2750 (n : Fin 5011) (hn : n.val = 2750) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2750 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2751 (n : Fin 5011) (hn : n.val = 2751) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2751 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2752 (n : Fin 5011) (hn : n.val = 2752) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2752 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2753 (n : Fin 5011) (hn : n.val = 2753) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2753 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2754 (n : Fin 5011) (hn : n.val = 2754) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2754 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2755 (n : Fin 5011) (hn : n.val = 2755) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2755 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2756 (n : Fin 5011) (hn : n.val = 2756) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2756 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2757 (n : Fin 5011) (hn : n.val = 2757) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2757 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2758 (n : Fin 5011) (hn : n.val = 2758) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2758 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2759 (n : Fin 5011) (hn : n.val = 2759) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2759 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2760 (n : Fin 5011) (hn : n.val = 2760) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2760 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2761 (n : Fin 5011) (hn : n.val = 2761) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2761 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2762 (n : Fin 5011) (hn : n.val = 2762) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2762 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2763 (n : Fin 5011) (hn : n.val = 2763) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2763 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2764 (n : Fin 5011) (hn : n.val = 2764) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2764 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2765 (n : Fin 5011) (hn : n.val = 2765) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2765 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2766 (n : Fin 5011) (hn : n.val = 2766) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2766 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2767 (n : Fin 5011) (hn : n.val = 2767) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2767 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2768 (n : Fin 5011) (hn : n.val = 2768) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2768 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2769 (n : Fin 5011) (hn : n.val = 2769) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2769 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2770 (n : Fin 5011) (hn : n.val = 2770) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2770 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2771 (n : Fin 5011) (hn : n.val = 2771) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2771 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2772 (n : Fin 5011) (hn : n.val = 2772) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2772 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2773 (n : Fin 5011) (hn : n.val = 2773) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2773 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2774 (n : Fin 5011) (hn : n.val = 2774) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2774 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2775 (n : Fin 5011) (hn : n.val = 2775) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2775 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2776 (n : Fin 5011) (hn : n.val = 2776) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2776 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2777 (n : Fin 5011) (hn : n.val = 2777) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2777 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2778 (n : Fin 5011) (hn : n.val = 2778) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2778 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2779 (n : Fin 5011) (hn : n.val = 2779) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2779 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2780 (n : Fin 5011) (hn : n.val = 2780) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2780 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2781 (n : Fin 5011) (hn : n.val = 2781) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2781 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2782 (n : Fin 5011) (hn : n.val = 2782) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2782 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2783 (n : Fin 5011) (hn : n.val = 2783) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2783 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2784 (n : Fin 5011) (hn : n.val = 2784) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2784 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2785 (n : Fin 5011) (hn : n.val = 2785) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2785 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2786 (n : Fin 5011) (hn : n.val = 2786) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2786 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2787 (n : Fin 5011) (hn : n.val = 2787) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2787 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2788 (n : Fin 5011) (hn : n.val = 2788) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2788 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2789 (n : Fin 5011) (hn : n.val = 2789) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2789 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2790 (n : Fin 5011) (hn : n.val = 2790) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2790 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2791 (n : Fin 5011) (hn : n.val = 2791) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2791 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2792 (n : Fin 5011) (hn : n.val = 2792) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2792 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2793 (n : Fin 5011) (hn : n.val = 2793) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2793 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2794 (n : Fin 5011) (hn : n.val = 2794) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2794 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2795 (n : Fin 5011) (hn : n.val = 2795) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2795 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2796 (n : Fin 5011) (hn : n.val = 2796) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2796 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2797 (n : Fin 5011) (hn : n.val = 2797) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2797 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2798 (n : Fin 5011) (hn : n.val = 2798) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2798 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2799 (n : Fin 5011) (hn : n.val = 2799) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2799 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3100 (n : Fin 5011) (hn : n.val = 3100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3100 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3101 (n : Fin 5011) (hn : n.val = 3101) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3101 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3102 (n : Fin 5011) (hn : n.val = 3102) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3102 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3103 (n : Fin 5011) (hn : n.val = 3103) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3103 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3104 (n : Fin 5011) (hn : n.val = 3104) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3104 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3105 (n : Fin 5011) (hn : n.val = 3105) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3105 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3106 (n : Fin 5011) (hn : n.val = 3106) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3106 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3107 (n : Fin 5011) (hn : n.val = 3107) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3107 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3108 (n : Fin 5011) (hn : n.val = 3108) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3108 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3109 (n : Fin 5011) (hn : n.val = 3109) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3109 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3110 (n : Fin 5011) (hn : n.val = 3110) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3110 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3111 (n : Fin 5011) (hn : n.val = 3111) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3111 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3112 (n : Fin 5011) (hn : n.val = 3112) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3112 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3113 (n : Fin 5011) (hn : n.val = 3113) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3113 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3114 (n : Fin 5011) (hn : n.val = 3114) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3114 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3115 (n : Fin 5011) (hn : n.val = 3115) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3115 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3116 (n : Fin 5011) (hn : n.val = 3116) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3116 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3117 (n : Fin 5011) (hn : n.val = 3117) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3117 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3118 (n : Fin 5011) (hn : n.val = 3118) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3118 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3119 (n : Fin 5011) (hn : n.val = 3119) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3119 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3120 (n : Fin 5011) (hn : n.val = 3120) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3120 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3121 (n : Fin 5011) (hn : n.val = 3121) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3121 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3122 (n : Fin 5011) (hn : n.val = 3122) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3122 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3123 (n : Fin 5011) (hn : n.val = 3123) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3123 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3124 (n : Fin 5011) (hn : n.val = 3124) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3124 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3125 (n : Fin 5011) (hn : n.val = 3125) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3125 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3126 (n : Fin 5011) (hn : n.val = 3126) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3126 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3127 (n : Fin 5011) (hn : n.val = 3127) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3127 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3128 (n : Fin 5011) (hn : n.val = 3128) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3128 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3129 (n : Fin 5011) (hn : n.val = 3129) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3129 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3130 (n : Fin 5011) (hn : n.val = 3130) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3130 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3131 (n : Fin 5011) (hn : n.val = 3131) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3131 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3132 (n : Fin 5011) (hn : n.val = 3132) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3132 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3133 (n : Fin 5011) (hn : n.val = 3133) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3133 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3134 (n : Fin 5011) (hn : n.val = 3134) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3134 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3135 (n : Fin 5011) (hn : n.val = 3135) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3135 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3136 (n : Fin 5011) (hn : n.val = 3136) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3136 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3137 (n : Fin 5011) (hn : n.val = 3137) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3137 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3138 (n : Fin 5011) (hn : n.val = 3138) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3138 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3139 (n : Fin 5011) (hn : n.val = 3139) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3139 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3140 (n : Fin 5011) (hn : n.val = 3140) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3140 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3141 (n : Fin 5011) (hn : n.val = 3141) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3141 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3142 (n : Fin 5011) (hn : n.val = 3142) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3142 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3143 (n : Fin 5011) (hn : n.val = 3143) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3143 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3144 (n : Fin 5011) (hn : n.val = 3144) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3144 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3145 (n : Fin 5011) (hn : n.val = 3145) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3145 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3146 (n : Fin 5011) (hn : n.val = 3146) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3146 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3147 (n : Fin 5011) (hn : n.val = 3147) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3147 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3148 (n : Fin 5011) (hn : n.val = 3148) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3148 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3149 (n : Fin 5011) (hn : n.val = 3149) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3149 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3150 (n : Fin 5011) (hn : n.val = 3150) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3150 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3151 (n : Fin 5011) (hn : n.val = 3151) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3151 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3152 (n : Fin 5011) (hn : n.val = 3152) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3152 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3153 (n : Fin 5011) (hn : n.val = 3153) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3153 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3154 (n : Fin 5011) (hn : n.val = 3154) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3154 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3155 (n : Fin 5011) (hn : n.val = 3155) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3155 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3156 (n : Fin 5011) (hn : n.val = 3156) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3156 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3157 (n : Fin 5011) (hn : n.val = 3157) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3157 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3158 (n : Fin 5011) (hn : n.val = 3158) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3158 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3159 (n : Fin 5011) (hn : n.val = 3159) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3159 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3160 (n : Fin 5011) (hn : n.val = 3160) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3160 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3161 (n : Fin 5011) (hn : n.val = 3161) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3161 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3162 (n : Fin 5011) (hn : n.val = 3162) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3162 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3163 (n : Fin 5011) (hn : n.val = 3163) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3163 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3164 (n : Fin 5011) (hn : n.val = 3164) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3164 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3165 (n : Fin 5011) (hn : n.val = 3165) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3165 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3166 (n : Fin 5011) (hn : n.val = 3166) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3166 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3167 (n : Fin 5011) (hn : n.val = 3167) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3167 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3168 (n : Fin 5011) (hn : n.val = 3168) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3168 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3169 (n : Fin 5011) (hn : n.val = 3169) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3169 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3170 (n : Fin 5011) (hn : n.val = 3170) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3170 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3171 (n : Fin 5011) (hn : n.val = 3171) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3171 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3172 (n : Fin 5011) (hn : n.val = 3172) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3172 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3173 (n : Fin 5011) (hn : n.val = 3173) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3173 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3174 (n : Fin 5011) (hn : n.val = 3174) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3174 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3175 (n : Fin 5011) (hn : n.val = 3175) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3175 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3176 (n : Fin 5011) (hn : n.val = 3176) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3176 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3177 (n : Fin 5011) (hn : n.val = 3177) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3177 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3178 (n : Fin 5011) (hn : n.val = 3178) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3178 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3179 (n : Fin 5011) (hn : n.val = 3179) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3179 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3180 (n : Fin 5011) (hn : n.val = 3180) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3180 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3181 (n : Fin 5011) (hn : n.val = 3181) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3181 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3182 (n : Fin 5011) (hn : n.val = 3182) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3182 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3183 (n : Fin 5011) (hn : n.val = 3183) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3183 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3184 (n : Fin 5011) (hn : n.val = 3184) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3184 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3185 (n : Fin 5011) (hn : n.val = 3185) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3185 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3186 (n : Fin 5011) (hn : n.val = 3186) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3186 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3187 (n : Fin 5011) (hn : n.val = 3187) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3187 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3188 (n : Fin 5011) (hn : n.val = 3188) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3188 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3189 (n : Fin 5011) (hn : n.val = 3189) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3189 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3190 (n : Fin 5011) (hn : n.val = 3190) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3190 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3191 (n : Fin 5011) (hn : n.val = 3191) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3191 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3192 (n : Fin 5011) (hn : n.val = 3192) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3192 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3193 (n : Fin 5011) (hn : n.val = 3193) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3193 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3194 (n : Fin 5011) (hn : n.val = 3194) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3194 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3195 (n : Fin 5011) (hn : n.val = 3195) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3195 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3196 (n : Fin 5011) (hn : n.val = 3196) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3196 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3197 (n : Fin 5011) (hn : n.val = 3197) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3197 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3198 (n : Fin 5011) (hn : n.val = 3198) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3198 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3199 (n : Fin 5011) (hn : n.val = 3199) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3199 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3500 (n : Fin 5011) (hn : n.val = 3500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3500 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3501 (n : Fin 5011) (hn : n.val = 3501) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3501 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3502 (n : Fin 5011) (hn : n.val = 3502) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3502 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3503 (n : Fin 5011) (hn : n.val = 3503) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3503 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3504 (n : Fin 5011) (hn : n.val = 3504) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3504 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3505 (n : Fin 5011) (hn : n.val = 3505) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3505 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3506 (n : Fin 5011) (hn : n.val = 3506) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3506 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3507 (n : Fin 5011) (hn : n.val = 3507) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3507 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3508 (n : Fin 5011) (hn : n.val = 3508) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3508 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3509 (n : Fin 5011) (hn : n.val = 3509) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3509 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3510 (n : Fin 5011) (hn : n.val = 3510) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3510 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3511 (n : Fin 5011) (hn : n.val = 3511) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3511 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3512 (n : Fin 5011) (hn : n.val = 3512) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3512 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3513 (n : Fin 5011) (hn : n.val = 3513) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3513 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3514 (n : Fin 5011) (hn : n.val = 3514) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3514 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3515 (n : Fin 5011) (hn : n.val = 3515) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3515 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3516 (n : Fin 5011) (hn : n.val = 3516) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3516 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3517 (n : Fin 5011) (hn : n.val = 3517) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3517 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3518 (n : Fin 5011) (hn : n.val = 3518) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3518 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3519 (n : Fin 5011) (hn : n.val = 3519) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3519 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3520 (n : Fin 5011) (hn : n.val = 3520) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3520 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3521 (n : Fin 5011) (hn : n.val = 3521) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3521 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3522 (n : Fin 5011) (hn : n.val = 3522) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3522 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3523 (n : Fin 5011) (hn : n.val = 3523) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3523 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3524 (n : Fin 5011) (hn : n.val = 3524) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3524 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3525 (n : Fin 5011) (hn : n.val = 3525) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3525 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3526 (n : Fin 5011) (hn : n.val = 3526) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3526 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3527 (n : Fin 5011) (hn : n.val = 3527) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3527 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3528 (n : Fin 5011) (hn : n.val = 3528) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3528 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3529 (n : Fin 5011) (hn : n.val = 3529) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3529 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3530 (n : Fin 5011) (hn : n.val = 3530) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3530 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3531 (n : Fin 5011) (hn : n.val = 3531) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3531 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3532 (n : Fin 5011) (hn : n.val = 3532) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3532 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3533 (n : Fin 5011) (hn : n.val = 3533) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3533 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3534 (n : Fin 5011) (hn : n.val = 3534) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3534 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3535 (n : Fin 5011) (hn : n.val = 3535) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3535 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3536 (n : Fin 5011) (hn : n.val = 3536) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3536 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3537 (n : Fin 5011) (hn : n.val = 3537) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3537 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3538 (n : Fin 5011) (hn : n.val = 3538) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3538 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3539 (n : Fin 5011) (hn : n.val = 3539) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3539 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3540 (n : Fin 5011) (hn : n.val = 3540) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3540 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3541 (n : Fin 5011) (hn : n.val = 3541) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3541 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3542 (n : Fin 5011) (hn : n.val = 3542) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3542 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3543 (n : Fin 5011) (hn : n.val = 3543) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3543 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3544 (n : Fin 5011) (hn : n.val = 3544) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3544 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3545 (n : Fin 5011) (hn : n.val = 3545) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3545 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3546 (n : Fin 5011) (hn : n.val = 3546) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3546 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3547 (n : Fin 5011) (hn : n.val = 3547) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3547 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3548 (n : Fin 5011) (hn : n.val = 3548) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3548 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3549 (n : Fin 5011) (hn : n.val = 3549) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3549 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3550 (n : Fin 5011) (hn : n.val = 3550) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3550 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3551 (n : Fin 5011) (hn : n.val = 3551) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3551 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3552 (n : Fin 5011) (hn : n.val = 3552) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3552 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3553 (n : Fin 5011) (hn : n.val = 3553) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3553 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3554 (n : Fin 5011) (hn : n.val = 3554) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3554 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3555 (n : Fin 5011) (hn : n.val = 3555) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3555 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3556 (n : Fin 5011) (hn : n.val = 3556) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3556 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3557 (n : Fin 5011) (hn : n.val = 3557) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3557 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3558 (n : Fin 5011) (hn : n.val = 3558) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3558 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3559 (n : Fin 5011) (hn : n.val = 3559) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3559 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3560 (n : Fin 5011) (hn : n.val = 3560) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3560 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3561 (n : Fin 5011) (hn : n.val = 3561) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3561 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3562 (n : Fin 5011) (hn : n.val = 3562) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3562 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3563 (n : Fin 5011) (hn : n.val = 3563) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3563 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3564 (n : Fin 5011) (hn : n.val = 3564) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3564 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3565 (n : Fin 5011) (hn : n.val = 3565) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3565 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3566 (n : Fin 5011) (hn : n.val = 3566) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3566 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3567 (n : Fin 5011) (hn : n.val = 3567) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3567 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3568 (n : Fin 5011) (hn : n.val = 3568) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3568 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3569 (n : Fin 5011) (hn : n.val = 3569) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3569 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3570 (n : Fin 5011) (hn : n.val = 3570) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3570 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3571 (n : Fin 5011) (hn : n.val = 3571) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3571 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3572 (n : Fin 5011) (hn : n.val = 3572) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3572 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3573 (n : Fin 5011) (hn : n.val = 3573) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3573 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3574 (n : Fin 5011) (hn : n.val = 3574) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3574 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3575 (n : Fin 5011) (hn : n.val = 3575) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3575 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3576 (n : Fin 5011) (hn : n.val = 3576) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3576 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3577 (n : Fin 5011) (hn : n.val = 3577) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3577 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3578 (n : Fin 5011) (hn : n.val = 3578) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3578 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3579 (n : Fin 5011) (hn : n.val = 3579) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3579 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3580 (n : Fin 5011) (hn : n.val = 3580) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3580 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3581 (n : Fin 5011) (hn : n.val = 3581) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3581 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3582 (n : Fin 5011) (hn : n.val = 3582) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3582 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3583 (n : Fin 5011) (hn : n.val = 3583) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3583 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3584 (n : Fin 5011) (hn : n.val = 3584) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3584 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3585 (n : Fin 5011) (hn : n.val = 3585) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3585 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3586 (n : Fin 5011) (hn : n.val = 3586) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3586 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3587 (n : Fin 5011) (hn : n.val = 3587) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3587 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3588 (n : Fin 5011) (hn : n.val = 3588) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3588 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3589 (n : Fin 5011) (hn : n.val = 3589) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3589 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3590 (n : Fin 5011) (hn : n.val = 3590) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3590 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3591 (n : Fin 5011) (hn : n.val = 3591) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3591 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3592 (n : Fin 5011) (hn : n.val = 3592) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3592 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3593 (n : Fin 5011) (hn : n.val = 3593) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3593 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3594 (n : Fin 5011) (hn : n.val = 3594) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3594 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3595 (n : Fin 5011) (hn : n.val = 3595) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3595 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3596 (n : Fin 5011) (hn : n.val = 3596) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3596 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3597 (n : Fin 5011) (hn : n.val = 3597) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3597 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3598 (n : Fin 5011) (hn : n.val = 3598) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3598 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3599 (n : Fin 5011) (hn : n.val = 3599) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3599 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3900 (n : Fin 5011) (hn : n.val = 3900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3900 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3901 (n : Fin 5011) (hn : n.val = 3901) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3901 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3902 (n : Fin 5011) (hn : n.val = 3902) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3902 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3903 (n : Fin 5011) (hn : n.val = 3903) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3903 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3904 (n : Fin 5011) (hn : n.val = 3904) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3904 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3905 (n : Fin 5011) (hn : n.val = 3905) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3905 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3906 (n : Fin 5011) (hn : n.val = 3906) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3906 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3907 (n : Fin 5011) (hn : n.val = 3907) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3907 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3908 (n : Fin 5011) (hn : n.val = 3908) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3908 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3909 (n : Fin 5011) (hn : n.val = 3909) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3909 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3910 (n : Fin 5011) (hn : n.val = 3910) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3910 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3911 (n : Fin 5011) (hn : n.val = 3911) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3911 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3912 (n : Fin 5011) (hn : n.val = 3912) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3912 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3913 (n : Fin 5011) (hn : n.val = 3913) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3913 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3914 (n : Fin 5011) (hn : n.val = 3914) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3914 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3915 (n : Fin 5011) (hn : n.val = 3915) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3915 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3916 (n : Fin 5011) (hn : n.val = 3916) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3916 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3917 (n : Fin 5011) (hn : n.val = 3917) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3917 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3918 (n : Fin 5011) (hn : n.val = 3918) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3918 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3919 (n : Fin 5011) (hn : n.val = 3919) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3919 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3920 (n : Fin 5011) (hn : n.val = 3920) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3920 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3921 (n : Fin 5011) (hn : n.val = 3921) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3921 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3922 (n : Fin 5011) (hn : n.val = 3922) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3922 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3923 (n : Fin 5011) (hn : n.val = 3923) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3923 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3924 (n : Fin 5011) (hn : n.val = 3924) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3924 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3925 (n : Fin 5011) (hn : n.val = 3925) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3925 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3926 (n : Fin 5011) (hn : n.val = 3926) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3926 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3927 (n : Fin 5011) (hn : n.val = 3927) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3927 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3928 (n : Fin 5011) (hn : n.val = 3928) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3928 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3929 (n : Fin 5011) (hn : n.val = 3929) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3929 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3930 (n : Fin 5011) (hn : n.val = 3930) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3930 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3931 (n : Fin 5011) (hn : n.val = 3931) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3931 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3932 (n : Fin 5011) (hn : n.val = 3932) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3932 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3933 (n : Fin 5011) (hn : n.val = 3933) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3933 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3934 (n : Fin 5011) (hn : n.val = 3934) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3934 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3935 (n : Fin 5011) (hn : n.val = 3935) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3935 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3936 (n : Fin 5011) (hn : n.val = 3936) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3936 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3937 (n : Fin 5011) (hn : n.val = 3937) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3937 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3938 (n : Fin 5011) (hn : n.val = 3938) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3938 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3939 (n : Fin 5011) (hn : n.val = 3939) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3939 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3940 (n : Fin 5011) (hn : n.val = 3940) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3940 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3941 (n : Fin 5011) (hn : n.val = 3941) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3941 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3942 (n : Fin 5011) (hn : n.val = 3942) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3942 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3943 (n : Fin 5011) (hn : n.val = 3943) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3943 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3944 (n : Fin 5011) (hn : n.val = 3944) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3944 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3945 (n : Fin 5011) (hn : n.val = 3945) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3945 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3946 (n : Fin 5011) (hn : n.val = 3946) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3946 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3947 (n : Fin 5011) (hn : n.val = 3947) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3947 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3948 (n : Fin 5011) (hn : n.val = 3948) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3948 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3949 (n : Fin 5011) (hn : n.val = 3949) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3949 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3950 (n : Fin 5011) (hn : n.val = 3950) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3950 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3951 (n : Fin 5011) (hn : n.val = 3951) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3951 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3952 (n : Fin 5011) (hn : n.val = 3952) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3952 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3953 (n : Fin 5011) (hn : n.val = 3953) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3953 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3954 (n : Fin 5011) (hn : n.val = 3954) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3954 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3955 (n : Fin 5011) (hn : n.val = 3955) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3955 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3956 (n : Fin 5011) (hn : n.val = 3956) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3956 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3957 (n : Fin 5011) (hn : n.val = 3957) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3957 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3958 (n : Fin 5011) (hn : n.val = 3958) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3958 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3959 (n : Fin 5011) (hn : n.val = 3959) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3959 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3960 (n : Fin 5011) (hn : n.val = 3960) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3960 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3961 (n : Fin 5011) (hn : n.val = 3961) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3961 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3962 (n : Fin 5011) (hn : n.val = 3962) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3962 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3963 (n : Fin 5011) (hn : n.val = 3963) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3963 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3964 (n : Fin 5011) (hn : n.val = 3964) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3964 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3965 (n : Fin 5011) (hn : n.val = 3965) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3965 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3966 (n : Fin 5011) (hn : n.val = 3966) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3966 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3967 (n : Fin 5011) (hn : n.val = 3967) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3967 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3968 (n : Fin 5011) (hn : n.val = 3968) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3968 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3969 (n : Fin 5011) (hn : n.val = 3969) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3969 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3970 (n : Fin 5011) (hn : n.val = 3970) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3970 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3971 (n : Fin 5011) (hn : n.val = 3971) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3971 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3972 (n : Fin 5011) (hn : n.val = 3972) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3972 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3973 (n : Fin 5011) (hn : n.val = 3973) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3973 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3974 (n : Fin 5011) (hn : n.val = 3974) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3974 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3975 (n : Fin 5011) (hn : n.val = 3975) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3975 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3976 (n : Fin 5011) (hn : n.val = 3976) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3976 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3977 (n : Fin 5011) (hn : n.val = 3977) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3977 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3978 (n : Fin 5011) (hn : n.val = 3978) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3978 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3979 (n : Fin 5011) (hn : n.val = 3979) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3979 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3980 (n : Fin 5011) (hn : n.val = 3980) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3980 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3981 (n : Fin 5011) (hn : n.val = 3981) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3981 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3982 (n : Fin 5011) (hn : n.val = 3982) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3982 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3983 (n : Fin 5011) (hn : n.val = 3983) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3983 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3984 (n : Fin 5011) (hn : n.val = 3984) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3984 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3985 (n : Fin 5011) (hn : n.val = 3985) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3985 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3986 (n : Fin 5011) (hn : n.val = 3986) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3986 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3987 (n : Fin 5011) (hn : n.val = 3987) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3987 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3988 (n : Fin 5011) (hn : n.val = 3988) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3988 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3989 (n : Fin 5011) (hn : n.val = 3989) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3989 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3990 (n : Fin 5011) (hn : n.val = 3990) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3990 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3991 (n : Fin 5011) (hn : n.val = 3991) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3991 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3992 (n : Fin 5011) (hn : n.val = 3992) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3992 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3993 (n : Fin 5011) (hn : n.val = 3993) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3993 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3994 (n : Fin 5011) (hn : n.val = 3994) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3994 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3995 (n : Fin 5011) (hn : n.val = 3995) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3995 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3996 (n : Fin 5011) (hn : n.val = 3996) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3996 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3997 (n : Fin 5011) (hn : n.val = 3997) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3997 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3998 (n : Fin 5011) (hn : n.val = 3998) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3998 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3999 (n : Fin 5011) (hn : n.val = 3999) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3999 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4300 (n : Fin 5011) (hn : n.val = 4300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4300 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4301 (n : Fin 5011) (hn : n.val = 4301) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4301 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4302 (n : Fin 5011) (hn : n.val = 4302) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4302 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4303 (n : Fin 5011) (hn : n.val = 4303) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4303 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4304 (n : Fin 5011) (hn : n.val = 4304) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4304 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4305 (n : Fin 5011) (hn : n.val = 4305) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4305 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4306 (n : Fin 5011) (hn : n.val = 4306) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4306 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4307 (n : Fin 5011) (hn : n.val = 4307) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4307 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4308 (n : Fin 5011) (hn : n.val = 4308) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4308 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4309 (n : Fin 5011) (hn : n.val = 4309) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4309 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4310 (n : Fin 5011) (hn : n.val = 4310) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4310 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4311 (n : Fin 5011) (hn : n.val = 4311) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4311 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4312 (n : Fin 5011) (hn : n.val = 4312) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4312 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4313 (n : Fin 5011) (hn : n.val = 4313) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4313 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4314 (n : Fin 5011) (hn : n.val = 4314) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4314 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4315 (n : Fin 5011) (hn : n.val = 4315) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4315 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4316 (n : Fin 5011) (hn : n.val = 4316) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4316 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4317 (n : Fin 5011) (hn : n.val = 4317) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4317 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4318 (n : Fin 5011) (hn : n.val = 4318) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4318 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4319 (n : Fin 5011) (hn : n.val = 4319) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4319 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4320 (n : Fin 5011) (hn : n.val = 4320) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4320 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4321 (n : Fin 5011) (hn : n.val = 4321) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4321 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4322 (n : Fin 5011) (hn : n.val = 4322) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4322 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4323 (n : Fin 5011) (hn : n.val = 4323) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4323 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4324 (n : Fin 5011) (hn : n.val = 4324) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4324 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4325 (n : Fin 5011) (hn : n.val = 4325) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4325 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4326 (n : Fin 5011) (hn : n.val = 4326) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4326 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4327 (n : Fin 5011) (hn : n.val = 4327) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4327 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4328 (n : Fin 5011) (hn : n.val = 4328) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4328 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4329 (n : Fin 5011) (hn : n.val = 4329) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4329 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4330 (n : Fin 5011) (hn : n.val = 4330) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4330 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4331 (n : Fin 5011) (hn : n.val = 4331) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4331 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4332 (n : Fin 5011) (hn : n.val = 4332) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4332 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4333 (n : Fin 5011) (hn : n.val = 4333) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4333 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4334 (n : Fin 5011) (hn : n.val = 4334) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4334 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4335 (n : Fin 5011) (hn : n.val = 4335) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4335 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4336 (n : Fin 5011) (hn : n.val = 4336) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4336 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4337 (n : Fin 5011) (hn : n.val = 4337) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4337 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4338 (n : Fin 5011) (hn : n.val = 4338) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4338 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4339 (n : Fin 5011) (hn : n.val = 4339) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4339 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4340 (n : Fin 5011) (hn : n.val = 4340) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4340 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4341 (n : Fin 5011) (hn : n.val = 4341) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4341 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4342 (n : Fin 5011) (hn : n.val = 4342) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4342 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4343 (n : Fin 5011) (hn : n.val = 4343) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4343 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4344 (n : Fin 5011) (hn : n.val = 4344) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4344 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4345 (n : Fin 5011) (hn : n.val = 4345) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4345 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4346 (n : Fin 5011) (hn : n.val = 4346) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4346 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4347 (n : Fin 5011) (hn : n.val = 4347) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4347 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4348 (n : Fin 5011) (hn : n.val = 4348) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4348 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4349 (n : Fin 5011) (hn : n.val = 4349) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4349 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4350 (n : Fin 5011) (hn : n.val = 4350) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4350 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4351 (n : Fin 5011) (hn : n.val = 4351) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4351 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4352 (n : Fin 5011) (hn : n.val = 4352) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4352 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4353 (n : Fin 5011) (hn : n.val = 4353) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4353 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4354 (n : Fin 5011) (hn : n.val = 4354) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4354 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4355 (n : Fin 5011) (hn : n.val = 4355) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4355 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4356 (n : Fin 5011) (hn : n.val = 4356) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4356 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4357 (n : Fin 5011) (hn : n.val = 4357) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4357 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4358 (n : Fin 5011) (hn : n.val = 4358) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4358 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4359 (n : Fin 5011) (hn : n.val = 4359) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4359 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4360 (n : Fin 5011) (hn : n.val = 4360) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4360 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4361 (n : Fin 5011) (hn : n.val = 4361) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4361 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4362 (n : Fin 5011) (hn : n.val = 4362) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4362 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4363 (n : Fin 5011) (hn : n.val = 4363) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4363 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4364 (n : Fin 5011) (hn : n.val = 4364) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4364 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4365 (n : Fin 5011) (hn : n.val = 4365) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4365 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4366 (n : Fin 5011) (hn : n.val = 4366) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4366 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4367 (n : Fin 5011) (hn : n.val = 4367) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4367 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4368 (n : Fin 5011) (hn : n.val = 4368) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4368 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4369 (n : Fin 5011) (hn : n.val = 4369) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4369 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4370 (n : Fin 5011) (hn : n.val = 4370) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4370 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4371 (n : Fin 5011) (hn : n.val = 4371) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4371 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4372 (n : Fin 5011) (hn : n.val = 4372) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4372 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4373 (n : Fin 5011) (hn : n.val = 4373) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4373 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4374 (n : Fin 5011) (hn : n.val = 4374) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4374 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4375 (n : Fin 5011) (hn : n.val = 4375) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4375 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4376 (n : Fin 5011) (hn : n.val = 4376) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4376 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4377 (n : Fin 5011) (hn : n.val = 4377) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4377 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4378 (n : Fin 5011) (hn : n.val = 4378) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4378 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4379 (n : Fin 5011) (hn : n.val = 4379) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4379 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4380 (n : Fin 5011) (hn : n.val = 4380) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4380 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4381 (n : Fin 5011) (hn : n.val = 4381) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4381 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4382 (n : Fin 5011) (hn : n.val = 4382) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4382 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4383 (n : Fin 5011) (hn : n.val = 4383) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4383 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4384 (n : Fin 5011) (hn : n.val = 4384) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4384 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4385 (n : Fin 5011) (hn : n.val = 4385) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4385 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4386 (n : Fin 5011) (hn : n.val = 4386) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4386 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4387 (n : Fin 5011) (hn : n.val = 4387) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4387 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4388 (n : Fin 5011) (hn : n.val = 4388) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4388 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4389 (n : Fin 5011) (hn : n.val = 4389) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4389 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4390 (n : Fin 5011) (hn : n.val = 4390) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4390 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4391 (n : Fin 5011) (hn : n.val = 4391) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4391 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4392 (n : Fin 5011) (hn : n.val = 4392) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4392 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4393 (n : Fin 5011) (hn : n.val = 4393) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4393 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4394 (n : Fin 5011) (hn : n.val = 4394) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4394 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4395 (n : Fin 5011) (hn : n.val = 4395) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4395 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4396 (n : Fin 5011) (hn : n.val = 4396) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4396 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4397 (n : Fin 5011) (hn : n.val = 4397) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4397 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4398 (n : Fin 5011) (hn : n.val = 4398) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4398 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4399 (n : Fin 5011) (hn : n.val = 4399) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4399 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4700 (n : Fin 5011) (hn : n.val = 4700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4700 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4701 (n : Fin 5011) (hn : n.val = 4701) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4701 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4702 (n : Fin 5011) (hn : n.val = 4702) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4702 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4703 (n : Fin 5011) (hn : n.val = 4703) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4703 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4704 (n : Fin 5011) (hn : n.val = 4704) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4704 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4705 (n : Fin 5011) (hn : n.val = 4705) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4705 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4706 (n : Fin 5011) (hn : n.val = 4706) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4706 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4707 (n : Fin 5011) (hn : n.val = 4707) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4707 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4708 (n : Fin 5011) (hn : n.val = 4708) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4708 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4709 (n : Fin 5011) (hn : n.val = 4709) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4709 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4710 (n : Fin 5011) (hn : n.val = 4710) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4710 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4711 (n : Fin 5011) (hn : n.val = 4711) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4711 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4712 (n : Fin 5011) (hn : n.val = 4712) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4712 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4713 (n : Fin 5011) (hn : n.val = 4713) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4713 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4714 (n : Fin 5011) (hn : n.val = 4714) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4714 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4715 (n : Fin 5011) (hn : n.val = 4715) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4715 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4716 (n : Fin 5011) (hn : n.val = 4716) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4716 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4717 (n : Fin 5011) (hn : n.val = 4717) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4717 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4718 (n : Fin 5011) (hn : n.val = 4718) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4718 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4719 (n : Fin 5011) (hn : n.val = 4719) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4719 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4720 (n : Fin 5011) (hn : n.val = 4720) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4720 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4721 (n : Fin 5011) (hn : n.val = 4721) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4721 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4722 (n : Fin 5011) (hn : n.val = 4722) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4722 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4723 (n : Fin 5011) (hn : n.val = 4723) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4723 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4724 (n : Fin 5011) (hn : n.val = 4724) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4724 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4725 (n : Fin 5011) (hn : n.val = 4725) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4725 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4726 (n : Fin 5011) (hn : n.val = 4726) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4726 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4727 (n : Fin 5011) (hn : n.val = 4727) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4727 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4728 (n : Fin 5011) (hn : n.val = 4728) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4728 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4729 (n : Fin 5011) (hn : n.val = 4729) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4729 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4730 (n : Fin 5011) (hn : n.val = 4730) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4730 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4731 (n : Fin 5011) (hn : n.val = 4731) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4731 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4732 (n : Fin 5011) (hn : n.val = 4732) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4732 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4733 (n : Fin 5011) (hn : n.val = 4733) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4733 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4734 (n : Fin 5011) (hn : n.val = 4734) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4734 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4735 (n : Fin 5011) (hn : n.val = 4735) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4735 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4736 (n : Fin 5011) (hn : n.val = 4736) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4736 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4737 (n : Fin 5011) (hn : n.val = 4737) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4737 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4738 (n : Fin 5011) (hn : n.val = 4738) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4738 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4739 (n : Fin 5011) (hn : n.val = 4739) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4739 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4740 (n : Fin 5011) (hn : n.val = 4740) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4740 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4741 (n : Fin 5011) (hn : n.val = 4741) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4741 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4742 (n : Fin 5011) (hn : n.val = 4742) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4742 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4743 (n : Fin 5011) (hn : n.val = 4743) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4743 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4744 (n : Fin 5011) (hn : n.val = 4744) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4744 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4745 (n : Fin 5011) (hn : n.val = 4745) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4745 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4746 (n : Fin 5011) (hn : n.val = 4746) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4746 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4747 (n : Fin 5011) (hn : n.val = 4747) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4747 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4748 (n : Fin 5011) (hn : n.val = 4748) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4748 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4749 (n : Fin 5011) (hn : n.val = 4749) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4749 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4750 (n : Fin 5011) (hn : n.val = 4750) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4750 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4751 (n : Fin 5011) (hn : n.val = 4751) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4751 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4752 (n : Fin 5011) (hn : n.val = 4752) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4752 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4753 (n : Fin 5011) (hn : n.val = 4753) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4753 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4754 (n : Fin 5011) (hn : n.val = 4754) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4754 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4755 (n : Fin 5011) (hn : n.val = 4755) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4755 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4756 (n : Fin 5011) (hn : n.val = 4756) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4756 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4757 (n : Fin 5011) (hn : n.val = 4757) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4757 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4758 (n : Fin 5011) (hn : n.val = 4758) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4758 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4759 (n : Fin 5011) (hn : n.val = 4759) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4759 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4760 (n : Fin 5011) (hn : n.val = 4760) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4760 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4761 (n : Fin 5011) (hn : n.val = 4761) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4761 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4762 (n : Fin 5011) (hn : n.val = 4762) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4762 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4763 (n : Fin 5011) (hn : n.val = 4763) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4763 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4764 (n : Fin 5011) (hn : n.val = 4764) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4764 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4765 (n : Fin 5011) (hn : n.val = 4765) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4765 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4766 (n : Fin 5011) (hn : n.val = 4766) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4766 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4767 (n : Fin 5011) (hn : n.val = 4767) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4767 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4768 (n : Fin 5011) (hn : n.val = 4768) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4768 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4769 (n : Fin 5011) (hn : n.val = 4769) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4769 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4770 (n : Fin 5011) (hn : n.val = 4770) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4770 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4771 (n : Fin 5011) (hn : n.val = 4771) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4771 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4772 (n : Fin 5011) (hn : n.val = 4772) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4772 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4773 (n : Fin 5011) (hn : n.val = 4773) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4773 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4774 (n : Fin 5011) (hn : n.val = 4774) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4774 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4775 (n : Fin 5011) (hn : n.val = 4775) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4775 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4776 (n : Fin 5011) (hn : n.val = 4776) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4776 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4777 (n : Fin 5011) (hn : n.val = 4777) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4777 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4778 (n : Fin 5011) (hn : n.val = 4778) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4778 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4779 (n : Fin 5011) (hn : n.val = 4779) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4779 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4780 (n : Fin 5011) (hn : n.val = 4780) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4780 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4781 (n : Fin 5011) (hn : n.val = 4781) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4781 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4782 (n : Fin 5011) (hn : n.val = 4782) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4782 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4783 (n : Fin 5011) (hn : n.val = 4783) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4783 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4784 (n : Fin 5011) (hn : n.val = 4784) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4784 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4785 (n : Fin 5011) (hn : n.val = 4785) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4785 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4786 (n : Fin 5011) (hn : n.val = 4786) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4786 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4787 (n : Fin 5011) (hn : n.val = 4787) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4787 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4788 (n : Fin 5011) (hn : n.val = 4788) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4788 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4789 (n : Fin 5011) (hn : n.val = 4789) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4789 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4790 (n : Fin 5011) (hn : n.val = 4790) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4790 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4791 (n : Fin 5011) (hn : n.val = 4791) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4791 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4792 (n : Fin 5011) (hn : n.val = 4792) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4792 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4793 (n : Fin 5011) (hn : n.val = 4793) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4793 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4794 (n : Fin 5011) (hn : n.val = 4794) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4794 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4795 (n : Fin 5011) (hn : n.val = 4795) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4795 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4796 (n : Fin 5011) (hn : n.val = 4796) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4796 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4797 (n : Fin 5011) (hn : n.val = 4797) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4797 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4798 (n : Fin 5011) (hn : n.val = 4798) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4798 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4799 (n : Fin 5011) (hn : n.val = 4799) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4799 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_block03 (n : Fin 5011) (hlo : 300 ≤ n.val) (hhi : n.val < 400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_0300 _ rfl
  · exact mem_iff_id_0301 _ rfl
  · exact mem_iff_id_0302 _ rfl
  · exact mem_iff_id_0303 _ rfl
  · exact mem_iff_id_0304 _ rfl
  · exact mem_iff_id_0305 _ rfl
  · exact mem_iff_id_0306 _ rfl
  · exact mem_iff_id_0307 _ rfl
  · exact mem_iff_id_0308 _ rfl
  · exact mem_iff_id_0309 _ rfl
  · exact mem_iff_id_0310 _ rfl
  · exact mem_iff_id_0311 _ rfl
  · exact mem_iff_id_0312 _ rfl
  · exact mem_iff_id_0313 _ rfl
  · exact mem_iff_id_0314 _ rfl
  · exact mem_iff_id_0315 _ rfl
  · exact mem_iff_id_0316 _ rfl
  · exact mem_iff_id_0317 _ rfl
  · exact mem_iff_id_0318 _ rfl
  · exact mem_iff_id_0319 _ rfl
  · exact mem_iff_id_0320 _ rfl
  · exact mem_iff_id_0321 _ rfl
  · exact mem_iff_id_0322 _ rfl
  · exact mem_iff_id_0323 _ rfl
  · exact mem_iff_id_0324 _ rfl
  · exact mem_iff_id_0325 _ rfl
  · exact mem_iff_id_0326 _ rfl
  · exact mem_iff_id_0327 _ rfl
  · exact mem_iff_id_0328 _ rfl
  · exact mem_iff_id_0329 _ rfl
  · exact mem_iff_id_0330 _ rfl
  · exact mem_iff_id_0331 _ rfl
  · exact mem_iff_id_0332 _ rfl
  · exact mem_iff_id_0333 _ rfl
  · exact mem_iff_id_0334 _ rfl
  · exact mem_iff_id_0335 _ rfl
  · exact mem_iff_id_0336 _ rfl
  · exact mem_iff_id_0337 _ rfl
  · exact mem_iff_id_0338 _ rfl
  · exact mem_iff_id_0339 _ rfl
  · exact mem_iff_id_0340 _ rfl
  · exact mem_iff_id_0341 _ rfl
  · exact mem_iff_id_0342 _ rfl
  · exact mem_iff_id_0343 _ rfl
  · exact mem_iff_id_0344 _ rfl
  · exact mem_iff_id_0345 _ rfl
  · exact mem_iff_id_0346 _ rfl
  · exact mem_iff_id_0347 _ rfl
  · exact mem_iff_id_0348 _ rfl
  · exact mem_iff_id_0349 _ rfl
  · exact mem_iff_id_0350 _ rfl
  · exact mem_iff_id_0351 _ rfl
  · exact mem_iff_id_0352 _ rfl
  · exact mem_iff_id_0353 _ rfl
  · exact mem_iff_id_0354 _ rfl
  · exact mem_iff_id_0355 _ rfl
  · exact mem_iff_id_0356 _ rfl
  · exact mem_iff_id_0357 _ rfl
  · exact mem_iff_id_0358 _ rfl
  · exact mem_iff_id_0359 _ rfl
  · exact mem_iff_id_0360 _ rfl
  · exact mem_iff_id_0361 _ rfl
  · exact mem_iff_id_0362 _ rfl
  · exact mem_iff_id_0363 _ rfl
  · exact mem_iff_id_0364 _ rfl
  · exact mem_iff_id_0365 _ rfl
  · exact mem_iff_id_0366 _ rfl
  · exact mem_iff_id_0367 _ rfl
  · exact mem_iff_id_0368 _ rfl
  · exact mem_iff_id_0369 _ rfl
  · exact mem_iff_id_0370 _ rfl
  · exact mem_iff_id_0371 _ rfl
  · exact mem_iff_id_0372 _ rfl
  · exact mem_iff_id_0373 _ rfl
  · exact mem_iff_id_0374 _ rfl
  · exact mem_iff_id_0375 _ rfl
  · exact mem_iff_id_0376 _ rfl
  · exact mem_iff_id_0377 _ rfl
  · exact mem_iff_id_0378 _ rfl
  · exact mem_iff_id_0379 _ rfl
  · exact mem_iff_id_0380 _ rfl
  · exact mem_iff_id_0381 _ rfl
  · exact mem_iff_id_0382 _ rfl
  · exact mem_iff_id_0383 _ rfl
  · exact mem_iff_id_0384 _ rfl
  · exact mem_iff_id_0385 _ rfl
  · exact mem_iff_id_0386 _ rfl
  · exact mem_iff_id_0387 _ rfl
  · exact mem_iff_id_0388 _ rfl
  · exact mem_iff_id_0389 _ rfl
  · exact mem_iff_id_0390 _ rfl
  · exact mem_iff_id_0391 _ rfl
  · exact mem_iff_id_0392 _ rfl
  · exact mem_iff_id_0393 _ rfl
  · exact mem_iff_id_0394 _ rfl
  · exact mem_iff_id_0395 _ rfl
  · exact mem_iff_id_0396 _ rfl
  · exact mem_iff_id_0397 _ rfl
  · exact mem_iff_id_0398 _ rfl
  · exact mem_iff_id_0399 _ rfl

theorem mem_iff_block07 (n : Fin 5011) (hlo : 700 ≤ n.val) (hhi : n.val < 800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_0700 _ rfl
  · exact mem_iff_id_0701 _ rfl
  · exact mem_iff_id_0702 _ rfl
  · exact mem_iff_id_0703 _ rfl
  · exact mem_iff_id_0704 _ rfl
  · exact mem_iff_id_0705 _ rfl
  · exact mem_iff_id_0706 _ rfl
  · exact mem_iff_id_0707 _ rfl
  · exact mem_iff_id_0708 _ rfl
  · exact mem_iff_id_0709 _ rfl
  · exact mem_iff_id_0710 _ rfl
  · exact mem_iff_id_0711 _ rfl
  · exact mem_iff_id_0712 _ rfl
  · exact mem_iff_id_0713 _ rfl
  · exact mem_iff_id_0714 _ rfl
  · exact mem_iff_id_0715 _ rfl
  · exact mem_iff_id_0716 _ rfl
  · exact mem_iff_id_0717 _ rfl
  · exact mem_iff_id_0718 _ rfl
  · exact mem_iff_id_0719 _ rfl
  · exact mem_iff_id_0720 _ rfl
  · exact mem_iff_id_0721 _ rfl
  · exact mem_iff_id_0722 _ rfl
  · exact mem_iff_id_0723 _ rfl
  · exact mem_iff_id_0724 _ rfl
  · exact mem_iff_id_0725 _ rfl
  · exact mem_iff_id_0726 _ rfl
  · exact mem_iff_id_0727 _ rfl
  · exact mem_iff_id_0728 _ rfl
  · exact mem_iff_id_0729 _ rfl
  · exact mem_iff_id_0730 _ rfl
  · exact mem_iff_id_0731 _ rfl
  · exact mem_iff_id_0732 _ rfl
  · exact mem_iff_id_0733 _ rfl
  · exact mem_iff_id_0734 _ rfl
  · exact mem_iff_id_0735 _ rfl
  · exact mem_iff_id_0736 _ rfl
  · exact mem_iff_id_0737 _ rfl
  · exact mem_iff_id_0738 _ rfl
  · exact mem_iff_id_0739 _ rfl
  · exact mem_iff_id_0740 _ rfl
  · exact mem_iff_id_0741 _ rfl
  · exact mem_iff_id_0742 _ rfl
  · exact mem_iff_id_0743 _ rfl
  · exact mem_iff_id_0744 _ rfl
  · exact mem_iff_id_0745 _ rfl
  · exact mem_iff_id_0746 _ rfl
  · exact mem_iff_id_0747 _ rfl
  · exact mem_iff_id_0748 _ rfl
  · exact mem_iff_id_0749 _ rfl
  · exact mem_iff_id_0750 _ rfl
  · exact mem_iff_id_0751 _ rfl
  · exact mem_iff_id_0752 _ rfl
  · exact mem_iff_id_0753 _ rfl
  · exact mem_iff_id_0754 _ rfl
  · exact mem_iff_id_0755 _ rfl
  · exact mem_iff_id_0756 _ rfl
  · exact mem_iff_id_0757 _ rfl
  · exact mem_iff_id_0758 _ rfl
  · exact mem_iff_id_0759 _ rfl
  · exact mem_iff_id_0760 _ rfl
  · exact mem_iff_id_0761 _ rfl
  · exact mem_iff_id_0762 _ rfl
  · exact mem_iff_id_0763 _ rfl
  · exact mem_iff_id_0764 _ rfl
  · exact mem_iff_id_0765 _ rfl
  · exact mem_iff_id_0766 _ rfl
  · exact mem_iff_id_0767 _ rfl
  · exact mem_iff_id_0768 _ rfl
  · exact mem_iff_id_0769 _ rfl
  · exact mem_iff_id_0770 _ rfl
  · exact mem_iff_id_0771 _ rfl
  · exact mem_iff_id_0772 _ rfl
  · exact mem_iff_id_0773 _ rfl
  · exact mem_iff_id_0774 _ rfl
  · exact mem_iff_id_0775 _ rfl
  · exact mem_iff_id_0776 _ rfl
  · exact mem_iff_id_0777 _ rfl
  · exact mem_iff_id_0778 _ rfl
  · exact mem_iff_id_0779 _ rfl
  · exact mem_iff_id_0780 _ rfl
  · exact mem_iff_id_0781 _ rfl
  · exact mem_iff_id_0782 _ rfl
  · exact mem_iff_id_0783 _ rfl
  · exact mem_iff_id_0784 _ rfl
  · exact mem_iff_id_0785 _ rfl
  · exact mem_iff_id_0786 _ rfl
  · exact mem_iff_id_0787 _ rfl
  · exact mem_iff_id_0788 _ rfl
  · exact mem_iff_id_0789 _ rfl
  · exact mem_iff_id_0790 _ rfl
  · exact mem_iff_id_0791 _ rfl
  · exact mem_iff_id_0792 _ rfl
  · exact mem_iff_id_0793 _ rfl
  · exact mem_iff_id_0794 _ rfl
  · exact mem_iff_id_0795 _ rfl
  · exact mem_iff_id_0796 _ rfl
  · exact mem_iff_id_0797 _ rfl
  · exact mem_iff_id_0798 _ rfl
  · exact mem_iff_id_0799 _ rfl

theorem mem_iff_block11 (n : Fin 5011) (hlo : 1100 ≤ n.val) (hhi : n.val < 1200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_1100 _ rfl
  · exact mem_iff_id_1101 _ rfl
  · exact mem_iff_id_1102 _ rfl
  · exact mem_iff_id_1103 _ rfl
  · exact mem_iff_id_1104 _ rfl
  · exact mem_iff_id_1105 _ rfl
  · exact mem_iff_id_1106 _ rfl
  · exact mem_iff_id_1107 _ rfl
  · exact mem_iff_id_1108 _ rfl
  · exact mem_iff_id_1109 _ rfl
  · exact mem_iff_id_1110 _ rfl
  · exact mem_iff_id_1111 _ rfl
  · exact mem_iff_id_1112 _ rfl
  · exact mem_iff_id_1113 _ rfl
  · exact mem_iff_id_1114 _ rfl
  · exact mem_iff_id_1115 _ rfl
  · exact mem_iff_id_1116 _ rfl
  · exact mem_iff_id_1117 _ rfl
  · exact mem_iff_id_1118 _ rfl
  · exact mem_iff_id_1119 _ rfl
  · exact mem_iff_id_1120 _ rfl
  · exact mem_iff_id_1121 _ rfl
  · exact mem_iff_id_1122 _ rfl
  · exact mem_iff_id_1123 _ rfl
  · exact mem_iff_id_1124 _ rfl
  · exact mem_iff_id_1125 _ rfl
  · exact mem_iff_id_1126 _ rfl
  · exact mem_iff_id_1127 _ rfl
  · exact mem_iff_id_1128 _ rfl
  · exact mem_iff_id_1129 _ rfl
  · exact mem_iff_id_1130 _ rfl
  · exact mem_iff_id_1131 _ rfl
  · exact mem_iff_id_1132 _ rfl
  · exact mem_iff_id_1133 _ rfl
  · exact mem_iff_id_1134 _ rfl
  · exact mem_iff_id_1135 _ rfl
  · exact mem_iff_id_1136 _ rfl
  · exact mem_iff_id_1137 _ rfl
  · exact mem_iff_id_1138 _ rfl
  · exact mem_iff_id_1139 _ rfl
  · exact mem_iff_id_1140 _ rfl
  · exact mem_iff_id_1141 _ rfl
  · exact mem_iff_id_1142 _ rfl
  · exact mem_iff_id_1143 _ rfl
  · exact mem_iff_id_1144 _ rfl
  · exact mem_iff_id_1145 _ rfl
  · exact mem_iff_id_1146 _ rfl
  · exact mem_iff_id_1147 _ rfl
  · exact mem_iff_id_1148 _ rfl
  · exact mem_iff_id_1149 _ rfl
  · exact mem_iff_id_1150 _ rfl
  · exact mem_iff_id_1151 _ rfl
  · exact mem_iff_id_1152 _ rfl
  · exact mem_iff_id_1153 _ rfl
  · exact mem_iff_id_1154 _ rfl
  · exact mem_iff_id_1155 _ rfl
  · exact mem_iff_id_1156 _ rfl
  · exact mem_iff_id_1157 _ rfl
  · exact mem_iff_id_1158 _ rfl
  · exact mem_iff_id_1159 _ rfl
  · exact mem_iff_id_1160 _ rfl
  · exact mem_iff_id_1161 _ rfl
  · exact mem_iff_id_1162 _ rfl
  · exact mem_iff_id_1163 _ rfl
  · exact mem_iff_id_1164 _ rfl
  · exact mem_iff_id_1165 _ rfl
  · exact mem_iff_id_1166 _ rfl
  · exact mem_iff_id_1167 _ rfl
  · exact mem_iff_id_1168 _ rfl
  · exact mem_iff_id_1169 _ rfl
  · exact mem_iff_id_1170 _ rfl
  · exact mem_iff_id_1171 _ rfl
  · exact mem_iff_id_1172 _ rfl
  · exact mem_iff_id_1173 _ rfl
  · exact mem_iff_id_1174 _ rfl
  · exact mem_iff_id_1175 _ rfl
  · exact mem_iff_id_1176 _ rfl
  · exact mem_iff_id_1177 _ rfl
  · exact mem_iff_id_1178 _ rfl
  · exact mem_iff_id_1179 _ rfl
  · exact mem_iff_id_1180 _ rfl
  · exact mem_iff_id_1181 _ rfl
  · exact mem_iff_id_1182 _ rfl
  · exact mem_iff_id_1183 _ rfl
  · exact mem_iff_id_1184 _ rfl
  · exact mem_iff_id_1185 _ rfl
  · exact mem_iff_id_1186 _ rfl
  · exact mem_iff_id_1187 _ rfl
  · exact mem_iff_id_1188 _ rfl
  · exact mem_iff_id_1189 _ rfl
  · exact mem_iff_id_1190 _ rfl
  · exact mem_iff_id_1191 _ rfl
  · exact mem_iff_id_1192 _ rfl
  · exact mem_iff_id_1193 _ rfl
  · exact mem_iff_id_1194 _ rfl
  · exact mem_iff_id_1195 _ rfl
  · exact mem_iff_id_1196 _ rfl
  · exact mem_iff_id_1197 _ rfl
  · exact mem_iff_id_1198 _ rfl
  · exact mem_iff_id_1199 _ rfl

theorem mem_iff_block15 (n : Fin 5011) (hlo : 1500 ≤ n.val) (hhi : n.val < 1600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_1500 _ rfl
  · exact mem_iff_id_1501 _ rfl
  · exact mem_iff_id_1502 _ rfl
  · exact mem_iff_id_1503 _ rfl
  · exact mem_iff_id_1504 _ rfl
  · exact mem_iff_id_1505 _ rfl
  · exact mem_iff_id_1506 _ rfl
  · exact mem_iff_id_1507 _ rfl
  · exact mem_iff_id_1508 _ rfl
  · exact mem_iff_id_1509 _ rfl
  · exact mem_iff_id_1510 _ rfl
  · exact mem_iff_id_1511 _ rfl
  · exact mem_iff_id_1512 _ rfl
  · exact mem_iff_id_1513 _ rfl
  · exact mem_iff_id_1514 _ rfl
  · exact mem_iff_id_1515 _ rfl
  · exact mem_iff_id_1516 _ rfl
  · exact mem_iff_id_1517 _ rfl
  · exact mem_iff_id_1518 _ rfl
  · exact mem_iff_id_1519 _ rfl
  · exact mem_iff_id_1520 _ rfl
  · exact mem_iff_id_1521 _ rfl
  · exact mem_iff_id_1522 _ rfl
  · exact mem_iff_id_1523 _ rfl
  · exact mem_iff_id_1524 _ rfl
  · exact mem_iff_id_1525 _ rfl
  · exact mem_iff_id_1526 _ rfl
  · exact mem_iff_id_1527 _ rfl
  · exact mem_iff_id_1528 _ rfl
  · exact mem_iff_id_1529 _ rfl
  · exact mem_iff_id_1530 _ rfl
  · exact mem_iff_id_1531 _ rfl
  · exact mem_iff_id_1532 _ rfl
  · exact mem_iff_id_1533 _ rfl
  · exact mem_iff_id_1534 _ rfl
  · exact mem_iff_id_1535 _ rfl
  · exact mem_iff_id_1536 _ rfl
  · exact mem_iff_id_1537 _ rfl
  · exact mem_iff_id_1538 _ rfl
  · exact mem_iff_id_1539 _ rfl
  · exact mem_iff_id_1540 _ rfl
  · exact mem_iff_id_1541 _ rfl
  · exact mem_iff_id_1542 _ rfl
  · exact mem_iff_id_1543 _ rfl
  · exact mem_iff_id_1544 _ rfl
  · exact mem_iff_id_1545 _ rfl
  · exact mem_iff_id_1546 _ rfl
  · exact mem_iff_id_1547 _ rfl
  · exact mem_iff_id_1548 _ rfl
  · exact mem_iff_id_1549 _ rfl
  · exact mem_iff_id_1550 _ rfl
  · exact mem_iff_id_1551 _ rfl
  · exact mem_iff_id_1552 _ rfl
  · exact mem_iff_id_1553 _ rfl
  · exact mem_iff_id_1554 _ rfl
  · exact mem_iff_id_1555 _ rfl
  · exact mem_iff_id_1556 _ rfl
  · exact mem_iff_id_1557 _ rfl
  · exact mem_iff_id_1558 _ rfl
  · exact mem_iff_id_1559 _ rfl
  · exact mem_iff_id_1560 _ rfl
  · exact mem_iff_id_1561 _ rfl
  · exact mem_iff_id_1562 _ rfl
  · exact mem_iff_id_1563 _ rfl
  · exact mem_iff_id_1564 _ rfl
  · exact mem_iff_id_1565 _ rfl
  · exact mem_iff_id_1566 _ rfl
  · exact mem_iff_id_1567 _ rfl
  · exact mem_iff_id_1568 _ rfl
  · exact mem_iff_id_1569 _ rfl
  · exact mem_iff_id_1570 _ rfl
  · exact mem_iff_id_1571 _ rfl
  · exact mem_iff_id_1572 _ rfl
  · exact mem_iff_id_1573 _ rfl
  · exact mem_iff_id_1574 _ rfl
  · exact mem_iff_id_1575 _ rfl
  · exact mem_iff_id_1576 _ rfl
  · exact mem_iff_id_1577 _ rfl
  · exact mem_iff_id_1578 _ rfl
  · exact mem_iff_id_1579 _ rfl
  · exact mem_iff_id_1580 _ rfl
  · exact mem_iff_id_1581 _ rfl
  · exact mem_iff_id_1582 _ rfl
  · exact mem_iff_id_1583 _ rfl
  · exact mem_iff_id_1584 _ rfl
  · exact mem_iff_id_1585 _ rfl
  · exact mem_iff_id_1586 _ rfl
  · exact mem_iff_id_1587 _ rfl
  · exact mem_iff_id_1588 _ rfl
  · exact mem_iff_id_1589 _ rfl
  · exact mem_iff_id_1590 _ rfl
  · exact mem_iff_id_1591 _ rfl
  · exact mem_iff_id_1592 _ rfl
  · exact mem_iff_id_1593 _ rfl
  · exact mem_iff_id_1594 _ rfl
  · exact mem_iff_id_1595 _ rfl
  · exact mem_iff_id_1596 _ rfl
  · exact mem_iff_id_1597 _ rfl
  · exact mem_iff_id_1598 _ rfl
  · exact mem_iff_id_1599 _ rfl

theorem mem_iff_block19 (n : Fin 5011) (hlo : 1900 ≤ n.val) (hhi : n.val < 2000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_1900 _ rfl
  · exact mem_iff_id_1901 _ rfl
  · exact mem_iff_id_1902 _ rfl
  · exact mem_iff_id_1903 _ rfl
  · exact mem_iff_id_1904 _ rfl
  · exact mem_iff_id_1905 _ rfl
  · exact mem_iff_id_1906 _ rfl
  · exact mem_iff_id_1907 _ rfl
  · exact mem_iff_id_1908 _ rfl
  · exact mem_iff_id_1909 _ rfl
  · exact mem_iff_id_1910 _ rfl
  · exact mem_iff_id_1911 _ rfl
  · exact mem_iff_id_1912 _ rfl
  · exact mem_iff_id_1913 _ rfl
  · exact mem_iff_id_1914 _ rfl
  · exact mem_iff_id_1915 _ rfl
  · exact mem_iff_id_1916 _ rfl
  · exact mem_iff_id_1917 _ rfl
  · exact mem_iff_id_1918 _ rfl
  · exact mem_iff_id_1919 _ rfl
  · exact mem_iff_id_1920 _ rfl
  · exact mem_iff_id_1921 _ rfl
  · exact mem_iff_id_1922 _ rfl
  · exact mem_iff_id_1923 _ rfl
  · exact mem_iff_id_1924 _ rfl
  · exact mem_iff_id_1925 _ rfl
  · exact mem_iff_id_1926 _ rfl
  · exact mem_iff_id_1927 _ rfl
  · exact mem_iff_id_1928 _ rfl
  · exact mem_iff_id_1929 _ rfl
  · exact mem_iff_id_1930 _ rfl
  · exact mem_iff_id_1931 _ rfl
  · exact mem_iff_id_1932 _ rfl
  · exact mem_iff_id_1933 _ rfl
  · exact mem_iff_id_1934 _ rfl
  · exact mem_iff_id_1935 _ rfl
  · exact mem_iff_id_1936 _ rfl
  · exact mem_iff_id_1937 _ rfl
  · exact mem_iff_id_1938 _ rfl
  · exact mem_iff_id_1939 _ rfl
  · exact mem_iff_id_1940 _ rfl
  · exact mem_iff_id_1941 _ rfl
  · exact mem_iff_id_1942 _ rfl
  · exact mem_iff_id_1943 _ rfl
  · exact mem_iff_id_1944 _ rfl
  · exact mem_iff_id_1945 _ rfl
  · exact mem_iff_id_1946 _ rfl
  · exact mem_iff_id_1947 _ rfl
  · exact mem_iff_id_1948 _ rfl
  · exact mem_iff_id_1949 _ rfl
  · exact mem_iff_id_1950 _ rfl
  · exact mem_iff_id_1951 _ rfl
  · exact mem_iff_id_1952 _ rfl
  · exact mem_iff_id_1953 _ rfl
  · exact mem_iff_id_1954 _ rfl
  · exact mem_iff_id_1955 _ rfl
  · exact mem_iff_id_1956 _ rfl
  · exact mem_iff_id_1957 _ rfl
  · exact mem_iff_id_1958 _ rfl
  · exact mem_iff_id_1959 _ rfl
  · exact mem_iff_id_1960 _ rfl
  · exact mem_iff_id_1961 _ rfl
  · exact mem_iff_id_1962 _ rfl
  · exact mem_iff_id_1963 _ rfl
  · exact mem_iff_id_1964 _ rfl
  · exact mem_iff_id_1965 _ rfl
  · exact mem_iff_id_1966 _ rfl
  · exact mem_iff_id_1967 _ rfl
  · exact mem_iff_id_1968 _ rfl
  · exact mem_iff_id_1969 _ rfl
  · exact mem_iff_id_1970 _ rfl
  · exact mem_iff_id_1971 _ rfl
  · exact mem_iff_id_1972 _ rfl
  · exact mem_iff_id_1973 _ rfl
  · exact mem_iff_id_1974 _ rfl
  · exact mem_iff_id_1975 _ rfl
  · exact mem_iff_id_1976 _ rfl
  · exact mem_iff_id_1977 _ rfl
  · exact mem_iff_id_1978 _ rfl
  · exact mem_iff_id_1979 _ rfl
  · exact mem_iff_id_1980 _ rfl
  · exact mem_iff_id_1981 _ rfl
  · exact mem_iff_id_1982 _ rfl
  · exact mem_iff_id_1983 _ rfl
  · exact mem_iff_id_1984 _ rfl
  · exact mem_iff_id_1985 _ rfl
  · exact mem_iff_id_1986 _ rfl
  · exact mem_iff_id_1987 _ rfl
  · exact mem_iff_id_1988 _ rfl
  · exact mem_iff_id_1989 _ rfl
  · exact mem_iff_id_1990 _ rfl
  · exact mem_iff_id_1991 _ rfl
  · exact mem_iff_id_1992 _ rfl
  · exact mem_iff_id_1993 _ rfl
  · exact mem_iff_id_1994 _ rfl
  · exact mem_iff_id_1995 _ rfl
  · exact mem_iff_id_1996 _ rfl
  · exact mem_iff_id_1997 _ rfl
  · exact mem_iff_id_1998 _ rfl
  · exact mem_iff_id_1999 _ rfl

theorem mem_iff_block23 (n : Fin 5011) (hlo : 2300 ≤ n.val) (hhi : n.val < 2400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_2300 _ rfl
  · exact mem_iff_id_2301 _ rfl
  · exact mem_iff_id_2302 _ rfl
  · exact mem_iff_id_2303 _ rfl
  · exact mem_iff_id_2304 _ rfl
  · exact mem_iff_id_2305 _ rfl
  · exact mem_iff_id_2306 _ rfl
  · exact mem_iff_id_2307 _ rfl
  · exact mem_iff_id_2308 _ rfl
  · exact mem_iff_id_2309 _ rfl
  · exact mem_iff_id_2310 _ rfl
  · exact mem_iff_id_2311 _ rfl
  · exact mem_iff_id_2312 _ rfl
  · exact mem_iff_id_2313 _ rfl
  · exact mem_iff_id_2314 _ rfl
  · exact mem_iff_id_2315 _ rfl
  · exact mem_iff_id_2316 _ rfl
  · exact mem_iff_id_2317 _ rfl
  · exact mem_iff_id_2318 _ rfl
  · exact mem_iff_id_2319 _ rfl
  · exact mem_iff_id_2320 _ rfl
  · exact mem_iff_id_2321 _ rfl
  · exact mem_iff_id_2322 _ rfl
  · exact mem_iff_id_2323 _ rfl
  · exact mem_iff_id_2324 _ rfl
  · exact mem_iff_id_2325 _ rfl
  · exact mem_iff_id_2326 _ rfl
  · exact mem_iff_id_2327 _ rfl
  · exact mem_iff_id_2328 _ rfl
  · exact mem_iff_id_2329 _ rfl
  · exact mem_iff_id_2330 _ rfl
  · exact mem_iff_id_2331 _ rfl
  · exact mem_iff_id_2332 _ rfl
  · exact mem_iff_id_2333 _ rfl
  · exact mem_iff_id_2334 _ rfl
  · exact mem_iff_id_2335 _ rfl
  · exact mem_iff_id_2336 _ rfl
  · exact mem_iff_id_2337 _ rfl
  · exact mem_iff_id_2338 _ rfl
  · exact mem_iff_id_2339 _ rfl
  · exact mem_iff_id_2340 _ rfl
  · exact mem_iff_id_2341 _ rfl
  · exact mem_iff_id_2342 _ rfl
  · exact mem_iff_id_2343 _ rfl
  · exact mem_iff_id_2344 _ rfl
  · exact mem_iff_id_2345 _ rfl
  · exact mem_iff_id_2346 _ rfl
  · exact mem_iff_id_2347 _ rfl
  · exact mem_iff_id_2348 _ rfl
  · exact mem_iff_id_2349 _ rfl
  · exact mem_iff_id_2350 _ rfl
  · exact mem_iff_id_2351 _ rfl
  · exact mem_iff_id_2352 _ rfl
  · exact mem_iff_id_2353 _ rfl
  · exact mem_iff_id_2354 _ rfl
  · exact mem_iff_id_2355 _ rfl
  · exact mem_iff_id_2356 _ rfl
  · exact mem_iff_id_2357 _ rfl
  · exact mem_iff_id_2358 _ rfl
  · exact mem_iff_id_2359 _ rfl
  · exact mem_iff_id_2360 _ rfl
  · exact mem_iff_id_2361 _ rfl
  · exact mem_iff_id_2362 _ rfl
  · exact mem_iff_id_2363 _ rfl
  · exact mem_iff_id_2364 _ rfl
  · exact mem_iff_id_2365 _ rfl
  · exact mem_iff_id_2366 _ rfl
  · exact mem_iff_id_2367 _ rfl
  · exact mem_iff_id_2368 _ rfl
  · exact mem_iff_id_2369 _ rfl
  · exact mem_iff_id_2370 _ rfl
  · exact mem_iff_id_2371 _ rfl
  · exact mem_iff_id_2372 _ rfl
  · exact mem_iff_id_2373 _ rfl
  · exact mem_iff_id_2374 _ rfl
  · exact mem_iff_id_2375 _ rfl
  · exact mem_iff_id_2376 _ rfl
  · exact mem_iff_id_2377 _ rfl
  · exact mem_iff_id_2378 _ rfl
  · exact mem_iff_id_2379 _ rfl
  · exact mem_iff_id_2380 _ rfl
  · exact mem_iff_id_2381 _ rfl
  · exact mem_iff_id_2382 _ rfl
  · exact mem_iff_id_2383 _ rfl
  · exact mem_iff_id_2384 _ rfl
  · exact mem_iff_id_2385 _ rfl
  · exact mem_iff_id_2386 _ rfl
  · exact mem_iff_id_2387 _ rfl
  · exact mem_iff_id_2388 _ rfl
  · exact mem_iff_id_2389 _ rfl
  · exact mem_iff_id_2390 _ rfl
  · exact mem_iff_id_2391 _ rfl
  · exact mem_iff_id_2392 _ rfl
  · exact mem_iff_id_2393 _ rfl
  · exact mem_iff_id_2394 _ rfl
  · exact mem_iff_id_2395 _ rfl
  · exact mem_iff_id_2396 _ rfl
  · exact mem_iff_id_2397 _ rfl
  · exact mem_iff_id_2398 _ rfl
  · exact mem_iff_id_2399 _ rfl

theorem mem_iff_block27 (n : Fin 5011) (hlo : 2700 ≤ n.val) (hhi : n.val < 2800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_2700 _ rfl
  · exact mem_iff_id_2701 _ rfl
  · exact mem_iff_id_2702 _ rfl
  · exact mem_iff_id_2703 _ rfl
  · exact mem_iff_id_2704 _ rfl
  · exact mem_iff_id_2705 _ rfl
  · exact mem_iff_id_2706 _ rfl
  · exact mem_iff_id_2707 _ rfl
  · exact mem_iff_id_2708 _ rfl
  · exact mem_iff_id_2709 _ rfl
  · exact mem_iff_id_2710 _ rfl
  · exact mem_iff_id_2711 _ rfl
  · exact mem_iff_id_2712 _ rfl
  · exact mem_iff_id_2713 _ rfl
  · exact mem_iff_id_2714 _ rfl
  · exact mem_iff_id_2715 _ rfl
  · exact mem_iff_id_2716 _ rfl
  · exact mem_iff_id_2717 _ rfl
  · exact mem_iff_id_2718 _ rfl
  · exact mem_iff_id_2719 _ rfl
  · exact mem_iff_id_2720 _ rfl
  · exact mem_iff_id_2721 _ rfl
  · exact mem_iff_id_2722 _ rfl
  · exact mem_iff_id_2723 _ rfl
  · exact mem_iff_id_2724 _ rfl
  · exact mem_iff_id_2725 _ rfl
  · exact mem_iff_id_2726 _ rfl
  · exact mem_iff_id_2727 _ rfl
  · exact mem_iff_id_2728 _ rfl
  · exact mem_iff_id_2729 _ rfl
  · exact mem_iff_id_2730 _ rfl
  · exact mem_iff_id_2731 _ rfl
  · exact mem_iff_id_2732 _ rfl
  · exact mem_iff_id_2733 _ rfl
  · exact mem_iff_id_2734 _ rfl
  · exact mem_iff_id_2735 _ rfl
  · exact mem_iff_id_2736 _ rfl
  · exact mem_iff_id_2737 _ rfl
  · exact mem_iff_id_2738 _ rfl
  · exact mem_iff_id_2739 _ rfl
  · exact mem_iff_id_2740 _ rfl
  · exact mem_iff_id_2741 _ rfl
  · exact mem_iff_id_2742 _ rfl
  · exact mem_iff_id_2743 _ rfl
  · exact mem_iff_id_2744 _ rfl
  · exact mem_iff_id_2745 _ rfl
  · exact mem_iff_id_2746 _ rfl
  · exact mem_iff_id_2747 _ rfl
  · exact mem_iff_id_2748 _ rfl
  · exact mem_iff_id_2749 _ rfl
  · exact mem_iff_id_2750 _ rfl
  · exact mem_iff_id_2751 _ rfl
  · exact mem_iff_id_2752 _ rfl
  · exact mem_iff_id_2753 _ rfl
  · exact mem_iff_id_2754 _ rfl
  · exact mem_iff_id_2755 _ rfl
  · exact mem_iff_id_2756 _ rfl
  · exact mem_iff_id_2757 _ rfl
  · exact mem_iff_id_2758 _ rfl
  · exact mem_iff_id_2759 _ rfl
  · exact mem_iff_id_2760 _ rfl
  · exact mem_iff_id_2761 _ rfl
  · exact mem_iff_id_2762 _ rfl
  · exact mem_iff_id_2763 _ rfl
  · exact mem_iff_id_2764 _ rfl
  · exact mem_iff_id_2765 _ rfl
  · exact mem_iff_id_2766 _ rfl
  · exact mem_iff_id_2767 _ rfl
  · exact mem_iff_id_2768 _ rfl
  · exact mem_iff_id_2769 _ rfl
  · exact mem_iff_id_2770 _ rfl
  · exact mem_iff_id_2771 _ rfl
  · exact mem_iff_id_2772 _ rfl
  · exact mem_iff_id_2773 _ rfl
  · exact mem_iff_id_2774 _ rfl
  · exact mem_iff_id_2775 _ rfl
  · exact mem_iff_id_2776 _ rfl
  · exact mem_iff_id_2777 _ rfl
  · exact mem_iff_id_2778 _ rfl
  · exact mem_iff_id_2779 _ rfl
  · exact mem_iff_id_2780 _ rfl
  · exact mem_iff_id_2781 _ rfl
  · exact mem_iff_id_2782 _ rfl
  · exact mem_iff_id_2783 _ rfl
  · exact mem_iff_id_2784 _ rfl
  · exact mem_iff_id_2785 _ rfl
  · exact mem_iff_id_2786 _ rfl
  · exact mem_iff_id_2787 _ rfl
  · exact mem_iff_id_2788 _ rfl
  · exact mem_iff_id_2789 _ rfl
  · exact mem_iff_id_2790 _ rfl
  · exact mem_iff_id_2791 _ rfl
  · exact mem_iff_id_2792 _ rfl
  · exact mem_iff_id_2793 _ rfl
  · exact mem_iff_id_2794 _ rfl
  · exact mem_iff_id_2795 _ rfl
  · exact mem_iff_id_2796 _ rfl
  · exact mem_iff_id_2797 _ rfl
  · exact mem_iff_id_2798 _ rfl
  · exact mem_iff_id_2799 _ rfl

theorem mem_iff_block31 (n : Fin 5011) (hlo : 3100 ≤ n.val) (hhi : n.val < 3200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_3100 _ rfl
  · exact mem_iff_id_3101 _ rfl
  · exact mem_iff_id_3102 _ rfl
  · exact mem_iff_id_3103 _ rfl
  · exact mem_iff_id_3104 _ rfl
  · exact mem_iff_id_3105 _ rfl
  · exact mem_iff_id_3106 _ rfl
  · exact mem_iff_id_3107 _ rfl
  · exact mem_iff_id_3108 _ rfl
  · exact mem_iff_id_3109 _ rfl
  · exact mem_iff_id_3110 _ rfl
  · exact mem_iff_id_3111 _ rfl
  · exact mem_iff_id_3112 _ rfl
  · exact mem_iff_id_3113 _ rfl
  · exact mem_iff_id_3114 _ rfl
  · exact mem_iff_id_3115 _ rfl
  · exact mem_iff_id_3116 _ rfl
  · exact mem_iff_id_3117 _ rfl
  · exact mem_iff_id_3118 _ rfl
  · exact mem_iff_id_3119 _ rfl
  · exact mem_iff_id_3120 _ rfl
  · exact mem_iff_id_3121 _ rfl
  · exact mem_iff_id_3122 _ rfl
  · exact mem_iff_id_3123 _ rfl
  · exact mem_iff_id_3124 _ rfl
  · exact mem_iff_id_3125 _ rfl
  · exact mem_iff_id_3126 _ rfl
  · exact mem_iff_id_3127 _ rfl
  · exact mem_iff_id_3128 _ rfl
  · exact mem_iff_id_3129 _ rfl
  · exact mem_iff_id_3130 _ rfl
  · exact mem_iff_id_3131 _ rfl
  · exact mem_iff_id_3132 _ rfl
  · exact mem_iff_id_3133 _ rfl
  · exact mem_iff_id_3134 _ rfl
  · exact mem_iff_id_3135 _ rfl
  · exact mem_iff_id_3136 _ rfl
  · exact mem_iff_id_3137 _ rfl
  · exact mem_iff_id_3138 _ rfl
  · exact mem_iff_id_3139 _ rfl
  · exact mem_iff_id_3140 _ rfl
  · exact mem_iff_id_3141 _ rfl
  · exact mem_iff_id_3142 _ rfl
  · exact mem_iff_id_3143 _ rfl
  · exact mem_iff_id_3144 _ rfl
  · exact mem_iff_id_3145 _ rfl
  · exact mem_iff_id_3146 _ rfl
  · exact mem_iff_id_3147 _ rfl
  · exact mem_iff_id_3148 _ rfl
  · exact mem_iff_id_3149 _ rfl
  · exact mem_iff_id_3150 _ rfl
  · exact mem_iff_id_3151 _ rfl
  · exact mem_iff_id_3152 _ rfl
  · exact mem_iff_id_3153 _ rfl
  · exact mem_iff_id_3154 _ rfl
  · exact mem_iff_id_3155 _ rfl
  · exact mem_iff_id_3156 _ rfl
  · exact mem_iff_id_3157 _ rfl
  · exact mem_iff_id_3158 _ rfl
  · exact mem_iff_id_3159 _ rfl
  · exact mem_iff_id_3160 _ rfl
  · exact mem_iff_id_3161 _ rfl
  · exact mem_iff_id_3162 _ rfl
  · exact mem_iff_id_3163 _ rfl
  · exact mem_iff_id_3164 _ rfl
  · exact mem_iff_id_3165 _ rfl
  · exact mem_iff_id_3166 _ rfl
  · exact mem_iff_id_3167 _ rfl
  · exact mem_iff_id_3168 _ rfl
  · exact mem_iff_id_3169 _ rfl
  · exact mem_iff_id_3170 _ rfl
  · exact mem_iff_id_3171 _ rfl
  · exact mem_iff_id_3172 _ rfl
  · exact mem_iff_id_3173 _ rfl
  · exact mem_iff_id_3174 _ rfl
  · exact mem_iff_id_3175 _ rfl
  · exact mem_iff_id_3176 _ rfl
  · exact mem_iff_id_3177 _ rfl
  · exact mem_iff_id_3178 _ rfl
  · exact mem_iff_id_3179 _ rfl
  · exact mem_iff_id_3180 _ rfl
  · exact mem_iff_id_3181 _ rfl
  · exact mem_iff_id_3182 _ rfl
  · exact mem_iff_id_3183 _ rfl
  · exact mem_iff_id_3184 _ rfl
  · exact mem_iff_id_3185 _ rfl
  · exact mem_iff_id_3186 _ rfl
  · exact mem_iff_id_3187 _ rfl
  · exact mem_iff_id_3188 _ rfl
  · exact mem_iff_id_3189 _ rfl
  · exact mem_iff_id_3190 _ rfl
  · exact mem_iff_id_3191 _ rfl
  · exact mem_iff_id_3192 _ rfl
  · exact mem_iff_id_3193 _ rfl
  · exact mem_iff_id_3194 _ rfl
  · exact mem_iff_id_3195 _ rfl
  · exact mem_iff_id_3196 _ rfl
  · exact mem_iff_id_3197 _ rfl
  · exact mem_iff_id_3198 _ rfl
  · exact mem_iff_id_3199 _ rfl

theorem mem_iff_block35 (n : Fin 5011) (hlo : 3500 ≤ n.val) (hhi : n.val < 3600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_3500 _ rfl
  · exact mem_iff_id_3501 _ rfl
  · exact mem_iff_id_3502 _ rfl
  · exact mem_iff_id_3503 _ rfl
  · exact mem_iff_id_3504 _ rfl
  · exact mem_iff_id_3505 _ rfl
  · exact mem_iff_id_3506 _ rfl
  · exact mem_iff_id_3507 _ rfl
  · exact mem_iff_id_3508 _ rfl
  · exact mem_iff_id_3509 _ rfl
  · exact mem_iff_id_3510 _ rfl
  · exact mem_iff_id_3511 _ rfl
  · exact mem_iff_id_3512 _ rfl
  · exact mem_iff_id_3513 _ rfl
  · exact mem_iff_id_3514 _ rfl
  · exact mem_iff_id_3515 _ rfl
  · exact mem_iff_id_3516 _ rfl
  · exact mem_iff_id_3517 _ rfl
  · exact mem_iff_id_3518 _ rfl
  · exact mem_iff_id_3519 _ rfl
  · exact mem_iff_id_3520 _ rfl
  · exact mem_iff_id_3521 _ rfl
  · exact mem_iff_id_3522 _ rfl
  · exact mem_iff_id_3523 _ rfl
  · exact mem_iff_id_3524 _ rfl
  · exact mem_iff_id_3525 _ rfl
  · exact mem_iff_id_3526 _ rfl
  · exact mem_iff_id_3527 _ rfl
  · exact mem_iff_id_3528 _ rfl
  · exact mem_iff_id_3529 _ rfl
  · exact mem_iff_id_3530 _ rfl
  · exact mem_iff_id_3531 _ rfl
  · exact mem_iff_id_3532 _ rfl
  · exact mem_iff_id_3533 _ rfl
  · exact mem_iff_id_3534 _ rfl
  · exact mem_iff_id_3535 _ rfl
  · exact mem_iff_id_3536 _ rfl
  · exact mem_iff_id_3537 _ rfl
  · exact mem_iff_id_3538 _ rfl
  · exact mem_iff_id_3539 _ rfl
  · exact mem_iff_id_3540 _ rfl
  · exact mem_iff_id_3541 _ rfl
  · exact mem_iff_id_3542 _ rfl
  · exact mem_iff_id_3543 _ rfl
  · exact mem_iff_id_3544 _ rfl
  · exact mem_iff_id_3545 _ rfl
  · exact mem_iff_id_3546 _ rfl
  · exact mem_iff_id_3547 _ rfl
  · exact mem_iff_id_3548 _ rfl
  · exact mem_iff_id_3549 _ rfl
  · exact mem_iff_id_3550 _ rfl
  · exact mem_iff_id_3551 _ rfl
  · exact mem_iff_id_3552 _ rfl
  · exact mem_iff_id_3553 _ rfl
  · exact mem_iff_id_3554 _ rfl
  · exact mem_iff_id_3555 _ rfl
  · exact mem_iff_id_3556 _ rfl
  · exact mem_iff_id_3557 _ rfl
  · exact mem_iff_id_3558 _ rfl
  · exact mem_iff_id_3559 _ rfl
  · exact mem_iff_id_3560 _ rfl
  · exact mem_iff_id_3561 _ rfl
  · exact mem_iff_id_3562 _ rfl
  · exact mem_iff_id_3563 _ rfl
  · exact mem_iff_id_3564 _ rfl
  · exact mem_iff_id_3565 _ rfl
  · exact mem_iff_id_3566 _ rfl
  · exact mem_iff_id_3567 _ rfl
  · exact mem_iff_id_3568 _ rfl
  · exact mem_iff_id_3569 _ rfl
  · exact mem_iff_id_3570 _ rfl
  · exact mem_iff_id_3571 _ rfl
  · exact mem_iff_id_3572 _ rfl
  · exact mem_iff_id_3573 _ rfl
  · exact mem_iff_id_3574 _ rfl
  · exact mem_iff_id_3575 _ rfl
  · exact mem_iff_id_3576 _ rfl
  · exact mem_iff_id_3577 _ rfl
  · exact mem_iff_id_3578 _ rfl
  · exact mem_iff_id_3579 _ rfl
  · exact mem_iff_id_3580 _ rfl
  · exact mem_iff_id_3581 _ rfl
  · exact mem_iff_id_3582 _ rfl
  · exact mem_iff_id_3583 _ rfl
  · exact mem_iff_id_3584 _ rfl
  · exact mem_iff_id_3585 _ rfl
  · exact mem_iff_id_3586 _ rfl
  · exact mem_iff_id_3587 _ rfl
  · exact mem_iff_id_3588 _ rfl
  · exact mem_iff_id_3589 _ rfl
  · exact mem_iff_id_3590 _ rfl
  · exact mem_iff_id_3591 _ rfl
  · exact mem_iff_id_3592 _ rfl
  · exact mem_iff_id_3593 _ rfl
  · exact mem_iff_id_3594 _ rfl
  · exact mem_iff_id_3595 _ rfl
  · exact mem_iff_id_3596 _ rfl
  · exact mem_iff_id_3597 _ rfl
  · exact mem_iff_id_3598 _ rfl
  · exact mem_iff_id_3599 _ rfl

theorem mem_iff_block39 (n : Fin 5011) (hlo : 3900 ≤ n.val) (hhi : n.val < 4000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_3900 _ rfl
  · exact mem_iff_id_3901 _ rfl
  · exact mem_iff_id_3902 _ rfl
  · exact mem_iff_id_3903 _ rfl
  · exact mem_iff_id_3904 _ rfl
  · exact mem_iff_id_3905 _ rfl
  · exact mem_iff_id_3906 _ rfl
  · exact mem_iff_id_3907 _ rfl
  · exact mem_iff_id_3908 _ rfl
  · exact mem_iff_id_3909 _ rfl
  · exact mem_iff_id_3910 _ rfl
  · exact mem_iff_id_3911 _ rfl
  · exact mem_iff_id_3912 _ rfl
  · exact mem_iff_id_3913 _ rfl
  · exact mem_iff_id_3914 _ rfl
  · exact mem_iff_id_3915 _ rfl
  · exact mem_iff_id_3916 _ rfl
  · exact mem_iff_id_3917 _ rfl
  · exact mem_iff_id_3918 _ rfl
  · exact mem_iff_id_3919 _ rfl
  · exact mem_iff_id_3920 _ rfl
  · exact mem_iff_id_3921 _ rfl
  · exact mem_iff_id_3922 _ rfl
  · exact mem_iff_id_3923 _ rfl
  · exact mem_iff_id_3924 _ rfl
  · exact mem_iff_id_3925 _ rfl
  · exact mem_iff_id_3926 _ rfl
  · exact mem_iff_id_3927 _ rfl
  · exact mem_iff_id_3928 _ rfl
  · exact mem_iff_id_3929 _ rfl
  · exact mem_iff_id_3930 _ rfl
  · exact mem_iff_id_3931 _ rfl
  · exact mem_iff_id_3932 _ rfl
  · exact mem_iff_id_3933 _ rfl
  · exact mem_iff_id_3934 _ rfl
  · exact mem_iff_id_3935 _ rfl
  · exact mem_iff_id_3936 _ rfl
  · exact mem_iff_id_3937 _ rfl
  · exact mem_iff_id_3938 _ rfl
  · exact mem_iff_id_3939 _ rfl
  · exact mem_iff_id_3940 _ rfl
  · exact mem_iff_id_3941 _ rfl
  · exact mem_iff_id_3942 _ rfl
  · exact mem_iff_id_3943 _ rfl
  · exact mem_iff_id_3944 _ rfl
  · exact mem_iff_id_3945 _ rfl
  · exact mem_iff_id_3946 _ rfl
  · exact mem_iff_id_3947 _ rfl
  · exact mem_iff_id_3948 _ rfl
  · exact mem_iff_id_3949 _ rfl
  · exact mem_iff_id_3950 _ rfl
  · exact mem_iff_id_3951 _ rfl
  · exact mem_iff_id_3952 _ rfl
  · exact mem_iff_id_3953 _ rfl
  · exact mem_iff_id_3954 _ rfl
  · exact mem_iff_id_3955 _ rfl
  · exact mem_iff_id_3956 _ rfl
  · exact mem_iff_id_3957 _ rfl
  · exact mem_iff_id_3958 _ rfl
  · exact mem_iff_id_3959 _ rfl
  · exact mem_iff_id_3960 _ rfl
  · exact mem_iff_id_3961 _ rfl
  · exact mem_iff_id_3962 _ rfl
  · exact mem_iff_id_3963 _ rfl
  · exact mem_iff_id_3964 _ rfl
  · exact mem_iff_id_3965 _ rfl
  · exact mem_iff_id_3966 _ rfl
  · exact mem_iff_id_3967 _ rfl
  · exact mem_iff_id_3968 _ rfl
  · exact mem_iff_id_3969 _ rfl
  · exact mem_iff_id_3970 _ rfl
  · exact mem_iff_id_3971 _ rfl
  · exact mem_iff_id_3972 _ rfl
  · exact mem_iff_id_3973 _ rfl
  · exact mem_iff_id_3974 _ rfl
  · exact mem_iff_id_3975 _ rfl
  · exact mem_iff_id_3976 _ rfl
  · exact mem_iff_id_3977 _ rfl
  · exact mem_iff_id_3978 _ rfl
  · exact mem_iff_id_3979 _ rfl
  · exact mem_iff_id_3980 _ rfl
  · exact mem_iff_id_3981 _ rfl
  · exact mem_iff_id_3982 _ rfl
  · exact mem_iff_id_3983 _ rfl
  · exact mem_iff_id_3984 _ rfl
  · exact mem_iff_id_3985 _ rfl
  · exact mem_iff_id_3986 _ rfl
  · exact mem_iff_id_3987 _ rfl
  · exact mem_iff_id_3988 _ rfl
  · exact mem_iff_id_3989 _ rfl
  · exact mem_iff_id_3990 _ rfl
  · exact mem_iff_id_3991 _ rfl
  · exact mem_iff_id_3992 _ rfl
  · exact mem_iff_id_3993 _ rfl
  · exact mem_iff_id_3994 _ rfl
  · exact mem_iff_id_3995 _ rfl
  · exact mem_iff_id_3996 _ rfl
  · exact mem_iff_id_3997 _ rfl
  · exact mem_iff_id_3998 _ rfl
  · exact mem_iff_id_3999 _ rfl

theorem mem_iff_block43 (n : Fin 5011) (hlo : 4300 ≤ n.val) (hhi : n.val < 4400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_4300 _ rfl
  · exact mem_iff_id_4301 _ rfl
  · exact mem_iff_id_4302 _ rfl
  · exact mem_iff_id_4303 _ rfl
  · exact mem_iff_id_4304 _ rfl
  · exact mem_iff_id_4305 _ rfl
  · exact mem_iff_id_4306 _ rfl
  · exact mem_iff_id_4307 _ rfl
  · exact mem_iff_id_4308 _ rfl
  · exact mem_iff_id_4309 _ rfl
  · exact mem_iff_id_4310 _ rfl
  · exact mem_iff_id_4311 _ rfl
  · exact mem_iff_id_4312 _ rfl
  · exact mem_iff_id_4313 _ rfl
  · exact mem_iff_id_4314 _ rfl
  · exact mem_iff_id_4315 _ rfl
  · exact mem_iff_id_4316 _ rfl
  · exact mem_iff_id_4317 _ rfl
  · exact mem_iff_id_4318 _ rfl
  · exact mem_iff_id_4319 _ rfl
  · exact mem_iff_id_4320 _ rfl
  · exact mem_iff_id_4321 _ rfl
  · exact mem_iff_id_4322 _ rfl
  · exact mem_iff_id_4323 _ rfl
  · exact mem_iff_id_4324 _ rfl
  · exact mem_iff_id_4325 _ rfl
  · exact mem_iff_id_4326 _ rfl
  · exact mem_iff_id_4327 _ rfl
  · exact mem_iff_id_4328 _ rfl
  · exact mem_iff_id_4329 _ rfl
  · exact mem_iff_id_4330 _ rfl
  · exact mem_iff_id_4331 _ rfl
  · exact mem_iff_id_4332 _ rfl
  · exact mem_iff_id_4333 _ rfl
  · exact mem_iff_id_4334 _ rfl
  · exact mem_iff_id_4335 _ rfl
  · exact mem_iff_id_4336 _ rfl
  · exact mem_iff_id_4337 _ rfl
  · exact mem_iff_id_4338 _ rfl
  · exact mem_iff_id_4339 _ rfl
  · exact mem_iff_id_4340 _ rfl
  · exact mem_iff_id_4341 _ rfl
  · exact mem_iff_id_4342 _ rfl
  · exact mem_iff_id_4343 _ rfl
  · exact mem_iff_id_4344 _ rfl
  · exact mem_iff_id_4345 _ rfl
  · exact mem_iff_id_4346 _ rfl
  · exact mem_iff_id_4347 _ rfl
  · exact mem_iff_id_4348 _ rfl
  · exact mem_iff_id_4349 _ rfl
  · exact mem_iff_id_4350 _ rfl
  · exact mem_iff_id_4351 _ rfl
  · exact mem_iff_id_4352 _ rfl
  · exact mem_iff_id_4353 _ rfl
  · exact mem_iff_id_4354 _ rfl
  · exact mem_iff_id_4355 _ rfl
  · exact mem_iff_id_4356 _ rfl
  · exact mem_iff_id_4357 _ rfl
  · exact mem_iff_id_4358 _ rfl
  · exact mem_iff_id_4359 _ rfl
  · exact mem_iff_id_4360 _ rfl
  · exact mem_iff_id_4361 _ rfl
  · exact mem_iff_id_4362 _ rfl
  · exact mem_iff_id_4363 _ rfl
  · exact mem_iff_id_4364 _ rfl
  · exact mem_iff_id_4365 _ rfl
  · exact mem_iff_id_4366 _ rfl
  · exact mem_iff_id_4367 _ rfl
  · exact mem_iff_id_4368 _ rfl
  · exact mem_iff_id_4369 _ rfl
  · exact mem_iff_id_4370 _ rfl
  · exact mem_iff_id_4371 _ rfl
  · exact mem_iff_id_4372 _ rfl
  · exact mem_iff_id_4373 _ rfl
  · exact mem_iff_id_4374 _ rfl
  · exact mem_iff_id_4375 _ rfl
  · exact mem_iff_id_4376 _ rfl
  · exact mem_iff_id_4377 _ rfl
  · exact mem_iff_id_4378 _ rfl
  · exact mem_iff_id_4379 _ rfl
  · exact mem_iff_id_4380 _ rfl
  · exact mem_iff_id_4381 _ rfl
  · exact mem_iff_id_4382 _ rfl
  · exact mem_iff_id_4383 _ rfl
  · exact mem_iff_id_4384 _ rfl
  · exact mem_iff_id_4385 _ rfl
  · exact mem_iff_id_4386 _ rfl
  · exact mem_iff_id_4387 _ rfl
  · exact mem_iff_id_4388 _ rfl
  · exact mem_iff_id_4389 _ rfl
  · exact mem_iff_id_4390 _ rfl
  · exact mem_iff_id_4391 _ rfl
  · exact mem_iff_id_4392 _ rfl
  · exact mem_iff_id_4393 _ rfl
  · exact mem_iff_id_4394 _ rfl
  · exact mem_iff_id_4395 _ rfl
  · exact mem_iff_id_4396 _ rfl
  · exact mem_iff_id_4397 _ rfl
  · exact mem_iff_id_4398 _ rfl
  · exact mem_iff_id_4399 _ rfl

theorem mem_iff_block47 (n : Fin 5011) (hlo : 4700 ≤ n.val) (hhi : n.val < 4800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_4700 _ rfl
  · exact mem_iff_id_4701 _ rfl
  · exact mem_iff_id_4702 _ rfl
  · exact mem_iff_id_4703 _ rfl
  · exact mem_iff_id_4704 _ rfl
  · exact mem_iff_id_4705 _ rfl
  · exact mem_iff_id_4706 _ rfl
  · exact mem_iff_id_4707 _ rfl
  · exact mem_iff_id_4708 _ rfl
  · exact mem_iff_id_4709 _ rfl
  · exact mem_iff_id_4710 _ rfl
  · exact mem_iff_id_4711 _ rfl
  · exact mem_iff_id_4712 _ rfl
  · exact mem_iff_id_4713 _ rfl
  · exact mem_iff_id_4714 _ rfl
  · exact mem_iff_id_4715 _ rfl
  · exact mem_iff_id_4716 _ rfl
  · exact mem_iff_id_4717 _ rfl
  · exact mem_iff_id_4718 _ rfl
  · exact mem_iff_id_4719 _ rfl
  · exact mem_iff_id_4720 _ rfl
  · exact mem_iff_id_4721 _ rfl
  · exact mem_iff_id_4722 _ rfl
  · exact mem_iff_id_4723 _ rfl
  · exact mem_iff_id_4724 _ rfl
  · exact mem_iff_id_4725 _ rfl
  · exact mem_iff_id_4726 _ rfl
  · exact mem_iff_id_4727 _ rfl
  · exact mem_iff_id_4728 _ rfl
  · exact mem_iff_id_4729 _ rfl
  · exact mem_iff_id_4730 _ rfl
  · exact mem_iff_id_4731 _ rfl
  · exact mem_iff_id_4732 _ rfl
  · exact mem_iff_id_4733 _ rfl
  · exact mem_iff_id_4734 _ rfl
  · exact mem_iff_id_4735 _ rfl
  · exact mem_iff_id_4736 _ rfl
  · exact mem_iff_id_4737 _ rfl
  · exact mem_iff_id_4738 _ rfl
  · exact mem_iff_id_4739 _ rfl
  · exact mem_iff_id_4740 _ rfl
  · exact mem_iff_id_4741 _ rfl
  · exact mem_iff_id_4742 _ rfl
  · exact mem_iff_id_4743 _ rfl
  · exact mem_iff_id_4744 _ rfl
  · exact mem_iff_id_4745 _ rfl
  · exact mem_iff_id_4746 _ rfl
  · exact mem_iff_id_4747 _ rfl
  · exact mem_iff_id_4748 _ rfl
  · exact mem_iff_id_4749 _ rfl
  · exact mem_iff_id_4750 _ rfl
  · exact mem_iff_id_4751 _ rfl
  · exact mem_iff_id_4752 _ rfl
  · exact mem_iff_id_4753 _ rfl
  · exact mem_iff_id_4754 _ rfl
  · exact mem_iff_id_4755 _ rfl
  · exact mem_iff_id_4756 _ rfl
  · exact mem_iff_id_4757 _ rfl
  · exact mem_iff_id_4758 _ rfl
  · exact mem_iff_id_4759 _ rfl
  · exact mem_iff_id_4760 _ rfl
  · exact mem_iff_id_4761 _ rfl
  · exact mem_iff_id_4762 _ rfl
  · exact mem_iff_id_4763 _ rfl
  · exact mem_iff_id_4764 _ rfl
  · exact mem_iff_id_4765 _ rfl
  · exact mem_iff_id_4766 _ rfl
  · exact mem_iff_id_4767 _ rfl
  · exact mem_iff_id_4768 _ rfl
  · exact mem_iff_id_4769 _ rfl
  · exact mem_iff_id_4770 _ rfl
  · exact mem_iff_id_4771 _ rfl
  · exact mem_iff_id_4772 _ rfl
  · exact mem_iff_id_4773 _ rfl
  · exact mem_iff_id_4774 _ rfl
  · exact mem_iff_id_4775 _ rfl
  · exact mem_iff_id_4776 _ rfl
  · exact mem_iff_id_4777 _ rfl
  · exact mem_iff_id_4778 _ rfl
  · exact mem_iff_id_4779 _ rfl
  · exact mem_iff_id_4780 _ rfl
  · exact mem_iff_id_4781 _ rfl
  · exact mem_iff_id_4782 _ rfl
  · exact mem_iff_id_4783 _ rfl
  · exact mem_iff_id_4784 _ rfl
  · exact mem_iff_id_4785 _ rfl
  · exact mem_iff_id_4786 _ rfl
  · exact mem_iff_id_4787 _ rfl
  · exact mem_iff_id_4788 _ rfl
  · exact mem_iff_id_4789 _ rfl
  · exact mem_iff_id_4790 _ rfl
  · exact mem_iff_id_4791 _ rfl
  · exact mem_iff_id_4792 _ rfl
  · exact mem_iff_id_4793 _ rfl
  · exact mem_iff_id_4794 _ rfl
  · exact mem_iff_id_4795 _ rfl
  · exact mem_iff_id_4796 _ rfl
  · exact mem_iff_id_4797 _ rfl
  · exact mem_iff_id_4798 _ rfl
  · exact mem_iff_id_4799 _ rfl

end
end N11Formalization.EnergyTerminalResidualCensus
