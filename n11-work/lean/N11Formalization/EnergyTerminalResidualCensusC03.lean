import N11Formalization.EnergyTerminalResidualCensusBase

/-! Census part 03.  Every single source index has its own theorem so no
declaration carries more than one heavy `decide +kernel`; each block
lemma (`mem_iff_blockNN`) delegates to its 100 per-index lemmas via
explicit bullets.  The exported interface is unchanged.
-/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensus
open Finset
noncomputable section

theorem mem_iff_id_0200 (n : Fin 5011) (hn : n.val = 200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 200 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0201 (n : Fin 5011) (hn : n.val = 201) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 201 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0202 (n : Fin 5011) (hn : n.val = 202) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 202 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0203 (n : Fin 5011) (hn : n.val = 203) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 203 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0204 (n : Fin 5011) (hn : n.val = 204) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 204 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0205 (n : Fin 5011) (hn : n.val = 205) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 205 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0206 (n : Fin 5011) (hn : n.val = 206) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 206 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0207 (n : Fin 5011) (hn : n.val = 207) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 207 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0208 (n : Fin 5011) (hn : n.val = 208) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 208 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0209 (n : Fin 5011) (hn : n.val = 209) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 209 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0210 (n : Fin 5011) (hn : n.val = 210) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 210 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0211 (n : Fin 5011) (hn : n.val = 211) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 211 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0212 (n : Fin 5011) (hn : n.val = 212) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 212 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0213 (n : Fin 5011) (hn : n.val = 213) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 213 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0214 (n : Fin 5011) (hn : n.val = 214) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 214 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0215 (n : Fin 5011) (hn : n.val = 215) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 215 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0216 (n : Fin 5011) (hn : n.val = 216) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 216 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0217 (n : Fin 5011) (hn : n.val = 217) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 217 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0218 (n : Fin 5011) (hn : n.val = 218) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 218 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0219 (n : Fin 5011) (hn : n.val = 219) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 219 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0220 (n : Fin 5011) (hn : n.val = 220) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 220 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0221 (n : Fin 5011) (hn : n.val = 221) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 221 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0222 (n : Fin 5011) (hn : n.val = 222) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 222 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0223 (n : Fin 5011) (hn : n.val = 223) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 223 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0224 (n : Fin 5011) (hn : n.val = 224) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 224 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0225 (n : Fin 5011) (hn : n.val = 225) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 225 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0226 (n : Fin 5011) (hn : n.val = 226) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 226 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0227 (n : Fin 5011) (hn : n.val = 227) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 227 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0228 (n : Fin 5011) (hn : n.val = 228) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 228 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0229 (n : Fin 5011) (hn : n.val = 229) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 229 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0230 (n : Fin 5011) (hn : n.val = 230) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 230 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0231 (n : Fin 5011) (hn : n.val = 231) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 231 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0232 (n : Fin 5011) (hn : n.val = 232) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 232 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0233 (n : Fin 5011) (hn : n.val = 233) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 233 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0234 (n : Fin 5011) (hn : n.val = 234) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 234 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0235 (n : Fin 5011) (hn : n.val = 235) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 235 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0236 (n : Fin 5011) (hn : n.val = 236) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 236 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0237 (n : Fin 5011) (hn : n.val = 237) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 237 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0238 (n : Fin 5011) (hn : n.val = 238) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 238 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0239 (n : Fin 5011) (hn : n.val = 239) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 239 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0240 (n : Fin 5011) (hn : n.val = 240) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 240 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0241 (n : Fin 5011) (hn : n.val = 241) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 241 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0242 (n : Fin 5011) (hn : n.val = 242) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 242 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0243 (n : Fin 5011) (hn : n.val = 243) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 243 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0244 (n : Fin 5011) (hn : n.val = 244) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 244 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0245 (n : Fin 5011) (hn : n.val = 245) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 245 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0246 (n : Fin 5011) (hn : n.val = 246) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 246 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0247 (n : Fin 5011) (hn : n.val = 247) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 247 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0248 (n : Fin 5011) (hn : n.val = 248) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 248 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0249 (n : Fin 5011) (hn : n.val = 249) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 249 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0250 (n : Fin 5011) (hn : n.val = 250) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 250 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0251 (n : Fin 5011) (hn : n.val = 251) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 251 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0252 (n : Fin 5011) (hn : n.val = 252) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 252 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0253 (n : Fin 5011) (hn : n.val = 253) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 253 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0254 (n : Fin 5011) (hn : n.val = 254) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 254 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0255 (n : Fin 5011) (hn : n.val = 255) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 255 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0256 (n : Fin 5011) (hn : n.val = 256) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 256 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0257 (n : Fin 5011) (hn : n.val = 257) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 257 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0258 (n : Fin 5011) (hn : n.val = 258) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 258 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0259 (n : Fin 5011) (hn : n.val = 259) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 259 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0260 (n : Fin 5011) (hn : n.val = 260) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 260 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0261 (n : Fin 5011) (hn : n.val = 261) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 261 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0262 (n : Fin 5011) (hn : n.val = 262) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 262 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0263 (n : Fin 5011) (hn : n.val = 263) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 263 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0264 (n : Fin 5011) (hn : n.val = 264) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 264 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0265 (n : Fin 5011) (hn : n.val = 265) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 265 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0266 (n : Fin 5011) (hn : n.val = 266) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 266 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0267 (n : Fin 5011) (hn : n.val = 267) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 267 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0268 (n : Fin 5011) (hn : n.val = 268) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 268 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0269 (n : Fin 5011) (hn : n.val = 269) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 269 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0270 (n : Fin 5011) (hn : n.val = 270) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 270 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0271 (n : Fin 5011) (hn : n.val = 271) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 271 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0272 (n : Fin 5011) (hn : n.val = 272) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 272 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0273 (n : Fin 5011) (hn : n.val = 273) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 273 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0274 (n : Fin 5011) (hn : n.val = 274) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 274 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0275 (n : Fin 5011) (hn : n.val = 275) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 275 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0276 (n : Fin 5011) (hn : n.val = 276) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 276 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0277 (n : Fin 5011) (hn : n.val = 277) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 277 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0278 (n : Fin 5011) (hn : n.val = 278) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 278 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0279 (n : Fin 5011) (hn : n.val = 279) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 279 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0280 (n : Fin 5011) (hn : n.val = 280) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 280 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0281 (n : Fin 5011) (hn : n.val = 281) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 281 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0282 (n : Fin 5011) (hn : n.val = 282) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 282 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0283 (n : Fin 5011) (hn : n.val = 283) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 283 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0284 (n : Fin 5011) (hn : n.val = 284) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 284 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0285 (n : Fin 5011) (hn : n.val = 285) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 285 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0286 (n : Fin 5011) (hn : n.val = 286) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 286 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0287 (n : Fin 5011) (hn : n.val = 287) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 287 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0288 (n : Fin 5011) (hn : n.val = 288) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 288 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0289 (n : Fin 5011) (hn : n.val = 289) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 289 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0290 (n : Fin 5011) (hn : n.val = 290) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 290 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0291 (n : Fin 5011) (hn : n.val = 291) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 291 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0292 (n : Fin 5011) (hn : n.val = 292) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 292 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0293 (n : Fin 5011) (hn : n.val = 293) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 293 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0294 (n : Fin 5011) (hn : n.val = 294) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 294 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0295 (n : Fin 5011) (hn : n.val = 295) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 295 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0296 (n : Fin 5011) (hn : n.val = 296) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 296 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0297 (n : Fin 5011) (hn : n.val = 297) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 297 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0298 (n : Fin 5011) (hn : n.val = 298) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 298 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0299 (n : Fin 5011) (hn : n.val = 299) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 299 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0600 (n : Fin 5011) (hn : n.val = 600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 600 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0601 (n : Fin 5011) (hn : n.val = 601) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 601 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0602 (n : Fin 5011) (hn : n.val = 602) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 602 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0603 (n : Fin 5011) (hn : n.val = 603) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 603 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0604 (n : Fin 5011) (hn : n.val = 604) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 604 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0605 (n : Fin 5011) (hn : n.val = 605) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 605 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0606 (n : Fin 5011) (hn : n.val = 606) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 606 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0607 (n : Fin 5011) (hn : n.val = 607) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 607 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0608 (n : Fin 5011) (hn : n.val = 608) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 608 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0609 (n : Fin 5011) (hn : n.val = 609) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 609 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0610 (n : Fin 5011) (hn : n.val = 610) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 610 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0611 (n : Fin 5011) (hn : n.val = 611) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 611 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0612 (n : Fin 5011) (hn : n.val = 612) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 612 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0613 (n : Fin 5011) (hn : n.val = 613) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 613 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0614 (n : Fin 5011) (hn : n.val = 614) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 614 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0615 (n : Fin 5011) (hn : n.val = 615) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 615 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0616 (n : Fin 5011) (hn : n.val = 616) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 616 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0617 (n : Fin 5011) (hn : n.val = 617) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 617 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0618 (n : Fin 5011) (hn : n.val = 618) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 618 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0619 (n : Fin 5011) (hn : n.val = 619) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 619 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0620 (n : Fin 5011) (hn : n.val = 620) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 620 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0621 (n : Fin 5011) (hn : n.val = 621) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 621 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0622 (n : Fin 5011) (hn : n.val = 622) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 622 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0623 (n : Fin 5011) (hn : n.val = 623) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 623 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0624 (n : Fin 5011) (hn : n.val = 624) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 624 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0625 (n : Fin 5011) (hn : n.val = 625) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 625 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0626 (n : Fin 5011) (hn : n.val = 626) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 626 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0627 (n : Fin 5011) (hn : n.val = 627) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 627 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0628 (n : Fin 5011) (hn : n.val = 628) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 628 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0629 (n : Fin 5011) (hn : n.val = 629) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 629 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0630 (n : Fin 5011) (hn : n.val = 630) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 630 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0631 (n : Fin 5011) (hn : n.val = 631) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 631 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0632 (n : Fin 5011) (hn : n.val = 632) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 632 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0633 (n : Fin 5011) (hn : n.val = 633) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 633 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0634 (n : Fin 5011) (hn : n.val = 634) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 634 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0635 (n : Fin 5011) (hn : n.val = 635) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 635 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0636 (n : Fin 5011) (hn : n.val = 636) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 636 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0637 (n : Fin 5011) (hn : n.val = 637) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 637 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0638 (n : Fin 5011) (hn : n.val = 638) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 638 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0639 (n : Fin 5011) (hn : n.val = 639) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 639 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0640 (n : Fin 5011) (hn : n.val = 640) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 640 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0641 (n : Fin 5011) (hn : n.val = 641) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 641 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0642 (n : Fin 5011) (hn : n.val = 642) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 642 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0643 (n : Fin 5011) (hn : n.val = 643) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 643 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0644 (n : Fin 5011) (hn : n.val = 644) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 644 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0645 (n : Fin 5011) (hn : n.val = 645) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 645 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0646 (n : Fin 5011) (hn : n.val = 646) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 646 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0647 (n : Fin 5011) (hn : n.val = 647) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 647 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0648 (n : Fin 5011) (hn : n.val = 648) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 648 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0649 (n : Fin 5011) (hn : n.val = 649) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 649 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0650 (n : Fin 5011) (hn : n.val = 650) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 650 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0651 (n : Fin 5011) (hn : n.val = 651) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 651 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0652 (n : Fin 5011) (hn : n.val = 652) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 652 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0653 (n : Fin 5011) (hn : n.val = 653) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 653 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0654 (n : Fin 5011) (hn : n.val = 654) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 654 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0655 (n : Fin 5011) (hn : n.val = 655) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 655 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0656 (n : Fin 5011) (hn : n.val = 656) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 656 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0657 (n : Fin 5011) (hn : n.val = 657) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 657 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0658 (n : Fin 5011) (hn : n.val = 658) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 658 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0659 (n : Fin 5011) (hn : n.val = 659) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 659 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0660 (n : Fin 5011) (hn : n.val = 660) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 660 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0661 (n : Fin 5011) (hn : n.val = 661) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 661 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0662 (n : Fin 5011) (hn : n.val = 662) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 662 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0663 (n : Fin 5011) (hn : n.val = 663) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 663 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0664 (n : Fin 5011) (hn : n.val = 664) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 664 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0665 (n : Fin 5011) (hn : n.val = 665) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 665 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0666 (n : Fin 5011) (hn : n.val = 666) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 666 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0667 (n : Fin 5011) (hn : n.val = 667) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 667 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0668 (n : Fin 5011) (hn : n.val = 668) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 668 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0669 (n : Fin 5011) (hn : n.val = 669) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 669 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0670 (n : Fin 5011) (hn : n.val = 670) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 670 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0671 (n : Fin 5011) (hn : n.val = 671) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 671 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0672 (n : Fin 5011) (hn : n.val = 672) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 672 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0673 (n : Fin 5011) (hn : n.val = 673) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 673 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0674 (n : Fin 5011) (hn : n.val = 674) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 674 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0675 (n : Fin 5011) (hn : n.val = 675) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 675 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0676 (n : Fin 5011) (hn : n.val = 676) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 676 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0677 (n : Fin 5011) (hn : n.val = 677) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 677 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0678 (n : Fin 5011) (hn : n.val = 678) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 678 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0679 (n : Fin 5011) (hn : n.val = 679) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 679 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0680 (n : Fin 5011) (hn : n.val = 680) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 680 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0681 (n : Fin 5011) (hn : n.val = 681) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 681 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0682 (n : Fin 5011) (hn : n.val = 682) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 682 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0683 (n : Fin 5011) (hn : n.val = 683) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 683 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0684 (n : Fin 5011) (hn : n.val = 684) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 684 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0685 (n : Fin 5011) (hn : n.val = 685) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 685 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0686 (n : Fin 5011) (hn : n.val = 686) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 686 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0687 (n : Fin 5011) (hn : n.val = 687) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 687 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0688 (n : Fin 5011) (hn : n.val = 688) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 688 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0689 (n : Fin 5011) (hn : n.val = 689) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 689 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0690 (n : Fin 5011) (hn : n.val = 690) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 690 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0691 (n : Fin 5011) (hn : n.val = 691) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 691 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0692 (n : Fin 5011) (hn : n.val = 692) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 692 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0693 (n : Fin 5011) (hn : n.val = 693) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 693 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0694 (n : Fin 5011) (hn : n.val = 694) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 694 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0695 (n : Fin 5011) (hn : n.val = 695) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 695 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0696 (n : Fin 5011) (hn : n.val = 696) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 696 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0697 (n : Fin 5011) (hn : n.val = 697) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 697 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0698 (n : Fin 5011) (hn : n.val = 698) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 698 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_0699 (n : Fin 5011) (hn : n.val = 699) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 699 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1000 (n : Fin 5011) (hn : n.val = 1000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1000 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1001 (n : Fin 5011) (hn : n.val = 1001) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1001 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1002 (n : Fin 5011) (hn : n.val = 1002) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1002 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1003 (n : Fin 5011) (hn : n.val = 1003) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1003 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1004 (n : Fin 5011) (hn : n.val = 1004) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1004 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1005 (n : Fin 5011) (hn : n.val = 1005) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1005 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1006 (n : Fin 5011) (hn : n.val = 1006) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1006 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1007 (n : Fin 5011) (hn : n.val = 1007) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1007 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1008 (n : Fin 5011) (hn : n.val = 1008) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1008 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1009 (n : Fin 5011) (hn : n.val = 1009) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1009 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1010 (n : Fin 5011) (hn : n.val = 1010) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1010 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1011 (n : Fin 5011) (hn : n.val = 1011) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1011 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1012 (n : Fin 5011) (hn : n.val = 1012) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1012 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1013 (n : Fin 5011) (hn : n.val = 1013) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1013 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1014 (n : Fin 5011) (hn : n.val = 1014) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1014 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1015 (n : Fin 5011) (hn : n.val = 1015) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1015 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1016 (n : Fin 5011) (hn : n.val = 1016) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1016 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1017 (n : Fin 5011) (hn : n.val = 1017) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1017 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1018 (n : Fin 5011) (hn : n.val = 1018) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1018 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1019 (n : Fin 5011) (hn : n.val = 1019) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1019 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1020 (n : Fin 5011) (hn : n.val = 1020) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1020 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1021 (n : Fin 5011) (hn : n.val = 1021) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1021 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1022 (n : Fin 5011) (hn : n.val = 1022) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1022 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1023 (n : Fin 5011) (hn : n.val = 1023) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1023 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1024 (n : Fin 5011) (hn : n.val = 1024) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1024 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1025 (n : Fin 5011) (hn : n.val = 1025) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1025 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1026 (n : Fin 5011) (hn : n.val = 1026) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1026 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1027 (n : Fin 5011) (hn : n.val = 1027) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1027 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1028 (n : Fin 5011) (hn : n.val = 1028) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1028 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1029 (n : Fin 5011) (hn : n.val = 1029) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1029 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1030 (n : Fin 5011) (hn : n.val = 1030) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1030 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1031 (n : Fin 5011) (hn : n.val = 1031) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1031 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1032 (n : Fin 5011) (hn : n.val = 1032) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1032 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1033 (n : Fin 5011) (hn : n.val = 1033) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1033 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1034 (n : Fin 5011) (hn : n.val = 1034) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1034 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1035 (n : Fin 5011) (hn : n.val = 1035) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1035 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1036 (n : Fin 5011) (hn : n.val = 1036) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1036 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1037 (n : Fin 5011) (hn : n.val = 1037) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1037 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1038 (n : Fin 5011) (hn : n.val = 1038) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1038 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1039 (n : Fin 5011) (hn : n.val = 1039) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1039 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1040 (n : Fin 5011) (hn : n.val = 1040) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1040 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1041 (n : Fin 5011) (hn : n.val = 1041) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1041 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1042 (n : Fin 5011) (hn : n.val = 1042) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1042 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1043 (n : Fin 5011) (hn : n.val = 1043) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1043 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1044 (n : Fin 5011) (hn : n.val = 1044) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1044 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1045 (n : Fin 5011) (hn : n.val = 1045) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1045 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1046 (n : Fin 5011) (hn : n.val = 1046) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1046 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1047 (n : Fin 5011) (hn : n.val = 1047) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1047 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1048 (n : Fin 5011) (hn : n.val = 1048) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1048 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1049 (n : Fin 5011) (hn : n.val = 1049) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1049 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1050 (n : Fin 5011) (hn : n.val = 1050) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1050 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1051 (n : Fin 5011) (hn : n.val = 1051) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1051 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1052 (n : Fin 5011) (hn : n.val = 1052) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1052 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1053 (n : Fin 5011) (hn : n.val = 1053) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1053 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1054 (n : Fin 5011) (hn : n.val = 1054) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1054 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1055 (n : Fin 5011) (hn : n.val = 1055) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1055 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1056 (n : Fin 5011) (hn : n.val = 1056) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1056 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1057 (n : Fin 5011) (hn : n.val = 1057) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1057 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1058 (n : Fin 5011) (hn : n.val = 1058) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1058 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1059 (n : Fin 5011) (hn : n.val = 1059) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1059 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1060 (n : Fin 5011) (hn : n.val = 1060) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1060 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1061 (n : Fin 5011) (hn : n.val = 1061) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1061 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1062 (n : Fin 5011) (hn : n.val = 1062) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1062 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1063 (n : Fin 5011) (hn : n.val = 1063) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1063 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1064 (n : Fin 5011) (hn : n.val = 1064) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1064 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1065 (n : Fin 5011) (hn : n.val = 1065) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1065 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1066 (n : Fin 5011) (hn : n.val = 1066) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1066 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1067 (n : Fin 5011) (hn : n.val = 1067) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1067 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1068 (n : Fin 5011) (hn : n.val = 1068) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1068 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1069 (n : Fin 5011) (hn : n.val = 1069) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1069 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1070 (n : Fin 5011) (hn : n.val = 1070) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1070 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1071 (n : Fin 5011) (hn : n.val = 1071) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1071 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1072 (n : Fin 5011) (hn : n.val = 1072) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1072 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1073 (n : Fin 5011) (hn : n.val = 1073) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1073 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1074 (n : Fin 5011) (hn : n.val = 1074) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1074 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1075 (n : Fin 5011) (hn : n.val = 1075) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1075 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1076 (n : Fin 5011) (hn : n.val = 1076) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1076 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1077 (n : Fin 5011) (hn : n.val = 1077) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1077 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1078 (n : Fin 5011) (hn : n.val = 1078) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1078 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1079 (n : Fin 5011) (hn : n.val = 1079) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1079 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1080 (n : Fin 5011) (hn : n.val = 1080) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1080 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1081 (n : Fin 5011) (hn : n.val = 1081) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1081 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1082 (n : Fin 5011) (hn : n.val = 1082) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1082 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1083 (n : Fin 5011) (hn : n.val = 1083) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1083 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1084 (n : Fin 5011) (hn : n.val = 1084) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1084 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1085 (n : Fin 5011) (hn : n.val = 1085) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1085 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1086 (n : Fin 5011) (hn : n.val = 1086) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1086 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1087 (n : Fin 5011) (hn : n.val = 1087) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1087 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1088 (n : Fin 5011) (hn : n.val = 1088) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1088 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1089 (n : Fin 5011) (hn : n.val = 1089) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1089 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1090 (n : Fin 5011) (hn : n.val = 1090) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1090 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1091 (n : Fin 5011) (hn : n.val = 1091) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1091 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1092 (n : Fin 5011) (hn : n.val = 1092) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1092 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1093 (n : Fin 5011) (hn : n.val = 1093) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1093 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1094 (n : Fin 5011) (hn : n.val = 1094) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1094 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1095 (n : Fin 5011) (hn : n.val = 1095) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1095 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1096 (n : Fin 5011) (hn : n.val = 1096) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1096 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1097 (n : Fin 5011) (hn : n.val = 1097) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1097 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1098 (n : Fin 5011) (hn : n.val = 1098) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1098 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1099 (n : Fin 5011) (hn : n.val = 1099) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1099 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1400 (n : Fin 5011) (hn : n.val = 1400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1400 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1401 (n : Fin 5011) (hn : n.val = 1401) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1401 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1402 (n : Fin 5011) (hn : n.val = 1402) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1402 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1403 (n : Fin 5011) (hn : n.val = 1403) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1403 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1404 (n : Fin 5011) (hn : n.val = 1404) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1404 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1405 (n : Fin 5011) (hn : n.val = 1405) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1405 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1406 (n : Fin 5011) (hn : n.val = 1406) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1406 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1407 (n : Fin 5011) (hn : n.val = 1407) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1407 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1408 (n : Fin 5011) (hn : n.val = 1408) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1408 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1409 (n : Fin 5011) (hn : n.val = 1409) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1409 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1410 (n : Fin 5011) (hn : n.val = 1410) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1410 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1411 (n : Fin 5011) (hn : n.val = 1411) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1411 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1412 (n : Fin 5011) (hn : n.val = 1412) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1412 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1413 (n : Fin 5011) (hn : n.val = 1413) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1413 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1414 (n : Fin 5011) (hn : n.val = 1414) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1414 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1415 (n : Fin 5011) (hn : n.val = 1415) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1415 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1416 (n : Fin 5011) (hn : n.val = 1416) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1416 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1417 (n : Fin 5011) (hn : n.val = 1417) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1417 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1418 (n : Fin 5011) (hn : n.val = 1418) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1418 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1419 (n : Fin 5011) (hn : n.val = 1419) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1419 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1420 (n : Fin 5011) (hn : n.val = 1420) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1420 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1421 (n : Fin 5011) (hn : n.val = 1421) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1421 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1422 (n : Fin 5011) (hn : n.val = 1422) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1422 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1423 (n : Fin 5011) (hn : n.val = 1423) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1423 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1424 (n : Fin 5011) (hn : n.val = 1424) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1424 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1425 (n : Fin 5011) (hn : n.val = 1425) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1425 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1426 (n : Fin 5011) (hn : n.val = 1426) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1426 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1427 (n : Fin 5011) (hn : n.val = 1427) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1427 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1428 (n : Fin 5011) (hn : n.val = 1428) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1428 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1429 (n : Fin 5011) (hn : n.val = 1429) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1429 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1430 (n : Fin 5011) (hn : n.val = 1430) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1430 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1431 (n : Fin 5011) (hn : n.val = 1431) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1431 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1432 (n : Fin 5011) (hn : n.val = 1432) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1432 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1433 (n : Fin 5011) (hn : n.val = 1433) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1433 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1434 (n : Fin 5011) (hn : n.val = 1434) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1434 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1435 (n : Fin 5011) (hn : n.val = 1435) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1435 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1436 (n : Fin 5011) (hn : n.val = 1436) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1436 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1437 (n : Fin 5011) (hn : n.val = 1437) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1437 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1438 (n : Fin 5011) (hn : n.val = 1438) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1438 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1439 (n : Fin 5011) (hn : n.val = 1439) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1439 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1440 (n : Fin 5011) (hn : n.val = 1440) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1440 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1441 (n : Fin 5011) (hn : n.val = 1441) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1441 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1442 (n : Fin 5011) (hn : n.val = 1442) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1442 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1443 (n : Fin 5011) (hn : n.val = 1443) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1443 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1444 (n : Fin 5011) (hn : n.val = 1444) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1444 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1445 (n : Fin 5011) (hn : n.val = 1445) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1445 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1446 (n : Fin 5011) (hn : n.val = 1446) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1446 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1447 (n : Fin 5011) (hn : n.val = 1447) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1447 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1448 (n : Fin 5011) (hn : n.val = 1448) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1448 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1449 (n : Fin 5011) (hn : n.val = 1449) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1449 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1450 (n : Fin 5011) (hn : n.val = 1450) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1450 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1451 (n : Fin 5011) (hn : n.val = 1451) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1451 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1452 (n : Fin 5011) (hn : n.val = 1452) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1452 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1453 (n : Fin 5011) (hn : n.val = 1453) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1453 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1454 (n : Fin 5011) (hn : n.val = 1454) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1454 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1455 (n : Fin 5011) (hn : n.val = 1455) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1455 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1456 (n : Fin 5011) (hn : n.val = 1456) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1456 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1457 (n : Fin 5011) (hn : n.val = 1457) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1457 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1458 (n : Fin 5011) (hn : n.val = 1458) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1458 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1459 (n : Fin 5011) (hn : n.val = 1459) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1459 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1460 (n : Fin 5011) (hn : n.val = 1460) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1460 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1461 (n : Fin 5011) (hn : n.val = 1461) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1461 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1462 (n : Fin 5011) (hn : n.val = 1462) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1462 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1463 (n : Fin 5011) (hn : n.val = 1463) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1463 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1464 (n : Fin 5011) (hn : n.val = 1464) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1464 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1465 (n : Fin 5011) (hn : n.val = 1465) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1465 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1466 (n : Fin 5011) (hn : n.val = 1466) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1466 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1467 (n : Fin 5011) (hn : n.val = 1467) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1467 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1468 (n : Fin 5011) (hn : n.val = 1468) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1468 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1469 (n : Fin 5011) (hn : n.val = 1469) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1469 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1470 (n : Fin 5011) (hn : n.val = 1470) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1470 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1471 (n : Fin 5011) (hn : n.val = 1471) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1471 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1472 (n : Fin 5011) (hn : n.val = 1472) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1472 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1473 (n : Fin 5011) (hn : n.val = 1473) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1473 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1474 (n : Fin 5011) (hn : n.val = 1474) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1474 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1475 (n : Fin 5011) (hn : n.val = 1475) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1475 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1476 (n : Fin 5011) (hn : n.val = 1476) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1476 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1477 (n : Fin 5011) (hn : n.val = 1477) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1477 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1478 (n : Fin 5011) (hn : n.val = 1478) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1478 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1479 (n : Fin 5011) (hn : n.val = 1479) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1479 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1480 (n : Fin 5011) (hn : n.val = 1480) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1480 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1481 (n : Fin 5011) (hn : n.val = 1481) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1481 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1482 (n : Fin 5011) (hn : n.val = 1482) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1482 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1483 (n : Fin 5011) (hn : n.val = 1483) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1483 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1484 (n : Fin 5011) (hn : n.val = 1484) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1484 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1485 (n : Fin 5011) (hn : n.val = 1485) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1485 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1486 (n : Fin 5011) (hn : n.val = 1486) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1486 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1487 (n : Fin 5011) (hn : n.val = 1487) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1487 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1488 (n : Fin 5011) (hn : n.val = 1488) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1488 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1489 (n : Fin 5011) (hn : n.val = 1489) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1489 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1490 (n : Fin 5011) (hn : n.val = 1490) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1490 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1491 (n : Fin 5011) (hn : n.val = 1491) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1491 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1492 (n : Fin 5011) (hn : n.val = 1492) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1492 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1493 (n : Fin 5011) (hn : n.val = 1493) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1493 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1494 (n : Fin 5011) (hn : n.val = 1494) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1494 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1495 (n : Fin 5011) (hn : n.val = 1495) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1495 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1496 (n : Fin 5011) (hn : n.val = 1496) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1496 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1497 (n : Fin 5011) (hn : n.val = 1497) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1497 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1498 (n : Fin 5011) (hn : n.val = 1498) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1498 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1499 (n : Fin 5011) (hn : n.val = 1499) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1499 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1800 (n : Fin 5011) (hn : n.val = 1800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1800 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1801 (n : Fin 5011) (hn : n.val = 1801) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1801 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1802 (n : Fin 5011) (hn : n.val = 1802) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1802 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1803 (n : Fin 5011) (hn : n.val = 1803) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1803 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1804 (n : Fin 5011) (hn : n.val = 1804) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1804 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1805 (n : Fin 5011) (hn : n.val = 1805) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1805 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1806 (n : Fin 5011) (hn : n.val = 1806) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1806 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1807 (n : Fin 5011) (hn : n.val = 1807) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1807 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1808 (n : Fin 5011) (hn : n.val = 1808) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1808 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1809 (n : Fin 5011) (hn : n.val = 1809) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1809 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1810 (n : Fin 5011) (hn : n.val = 1810) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1810 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1811 (n : Fin 5011) (hn : n.val = 1811) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1811 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1812 (n : Fin 5011) (hn : n.val = 1812) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1812 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1813 (n : Fin 5011) (hn : n.val = 1813) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1813 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1814 (n : Fin 5011) (hn : n.val = 1814) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1814 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1815 (n : Fin 5011) (hn : n.val = 1815) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1815 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1816 (n : Fin 5011) (hn : n.val = 1816) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1816 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1817 (n : Fin 5011) (hn : n.val = 1817) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1817 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1818 (n : Fin 5011) (hn : n.val = 1818) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1818 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1819 (n : Fin 5011) (hn : n.val = 1819) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1819 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1820 (n : Fin 5011) (hn : n.val = 1820) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1820 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1821 (n : Fin 5011) (hn : n.val = 1821) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1821 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1822 (n : Fin 5011) (hn : n.val = 1822) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1822 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1823 (n : Fin 5011) (hn : n.val = 1823) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1823 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1824 (n : Fin 5011) (hn : n.val = 1824) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1824 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1825 (n : Fin 5011) (hn : n.val = 1825) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1825 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1826 (n : Fin 5011) (hn : n.val = 1826) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1826 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1827 (n : Fin 5011) (hn : n.val = 1827) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1827 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1828 (n : Fin 5011) (hn : n.val = 1828) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1828 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1829 (n : Fin 5011) (hn : n.val = 1829) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1829 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1830 (n : Fin 5011) (hn : n.val = 1830) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1830 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1831 (n : Fin 5011) (hn : n.val = 1831) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1831 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1832 (n : Fin 5011) (hn : n.val = 1832) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1832 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1833 (n : Fin 5011) (hn : n.val = 1833) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1833 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1834 (n : Fin 5011) (hn : n.val = 1834) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1834 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1835 (n : Fin 5011) (hn : n.val = 1835) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1835 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1836 (n : Fin 5011) (hn : n.val = 1836) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1836 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1837 (n : Fin 5011) (hn : n.val = 1837) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1837 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1838 (n : Fin 5011) (hn : n.val = 1838) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1838 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1839 (n : Fin 5011) (hn : n.val = 1839) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1839 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1840 (n : Fin 5011) (hn : n.val = 1840) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1840 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1841 (n : Fin 5011) (hn : n.val = 1841) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1841 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1842 (n : Fin 5011) (hn : n.val = 1842) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1842 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1843 (n : Fin 5011) (hn : n.val = 1843) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1843 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1844 (n : Fin 5011) (hn : n.val = 1844) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1844 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1845 (n : Fin 5011) (hn : n.val = 1845) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1845 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1846 (n : Fin 5011) (hn : n.val = 1846) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1846 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1847 (n : Fin 5011) (hn : n.val = 1847) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1847 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1848 (n : Fin 5011) (hn : n.val = 1848) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1848 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1849 (n : Fin 5011) (hn : n.val = 1849) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1849 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1850 (n : Fin 5011) (hn : n.val = 1850) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1850 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1851 (n : Fin 5011) (hn : n.val = 1851) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1851 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1852 (n : Fin 5011) (hn : n.val = 1852) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1852 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1853 (n : Fin 5011) (hn : n.val = 1853) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1853 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1854 (n : Fin 5011) (hn : n.val = 1854) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1854 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1855 (n : Fin 5011) (hn : n.val = 1855) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1855 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1856 (n : Fin 5011) (hn : n.val = 1856) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1856 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1857 (n : Fin 5011) (hn : n.val = 1857) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1857 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1858 (n : Fin 5011) (hn : n.val = 1858) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1858 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1859 (n : Fin 5011) (hn : n.val = 1859) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1859 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1860 (n : Fin 5011) (hn : n.val = 1860) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1860 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1861 (n : Fin 5011) (hn : n.val = 1861) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1861 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1862 (n : Fin 5011) (hn : n.val = 1862) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1862 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1863 (n : Fin 5011) (hn : n.val = 1863) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1863 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1864 (n : Fin 5011) (hn : n.val = 1864) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1864 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1865 (n : Fin 5011) (hn : n.val = 1865) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1865 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1866 (n : Fin 5011) (hn : n.val = 1866) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1866 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1867 (n : Fin 5011) (hn : n.val = 1867) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1867 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1868 (n : Fin 5011) (hn : n.val = 1868) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1868 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1869 (n : Fin 5011) (hn : n.val = 1869) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1869 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1870 (n : Fin 5011) (hn : n.val = 1870) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1870 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1871 (n : Fin 5011) (hn : n.val = 1871) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1871 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1872 (n : Fin 5011) (hn : n.val = 1872) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1872 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1873 (n : Fin 5011) (hn : n.val = 1873) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1873 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1874 (n : Fin 5011) (hn : n.val = 1874) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1874 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1875 (n : Fin 5011) (hn : n.val = 1875) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1875 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1876 (n : Fin 5011) (hn : n.val = 1876) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1876 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1877 (n : Fin 5011) (hn : n.val = 1877) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1877 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1878 (n : Fin 5011) (hn : n.val = 1878) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1878 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1879 (n : Fin 5011) (hn : n.val = 1879) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1879 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1880 (n : Fin 5011) (hn : n.val = 1880) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1880 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1881 (n : Fin 5011) (hn : n.val = 1881) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1881 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1882 (n : Fin 5011) (hn : n.val = 1882) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1882 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1883 (n : Fin 5011) (hn : n.val = 1883) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1883 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1884 (n : Fin 5011) (hn : n.val = 1884) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1884 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1885 (n : Fin 5011) (hn : n.val = 1885) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1885 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1886 (n : Fin 5011) (hn : n.val = 1886) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1886 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1887 (n : Fin 5011) (hn : n.val = 1887) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1887 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1888 (n : Fin 5011) (hn : n.val = 1888) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1888 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1889 (n : Fin 5011) (hn : n.val = 1889) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1889 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1890 (n : Fin 5011) (hn : n.val = 1890) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1890 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1891 (n : Fin 5011) (hn : n.val = 1891) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1891 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1892 (n : Fin 5011) (hn : n.val = 1892) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1892 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1893 (n : Fin 5011) (hn : n.val = 1893) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1893 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1894 (n : Fin 5011) (hn : n.val = 1894) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1894 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1895 (n : Fin 5011) (hn : n.val = 1895) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1895 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1896 (n : Fin 5011) (hn : n.val = 1896) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1896 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1897 (n : Fin 5011) (hn : n.val = 1897) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1897 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1898 (n : Fin 5011) (hn : n.val = 1898) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1898 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_1899 (n : Fin 5011) (hn : n.val = 1899) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 1899 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2200 (n : Fin 5011) (hn : n.val = 2200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2200 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2201 (n : Fin 5011) (hn : n.val = 2201) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2201 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2202 (n : Fin 5011) (hn : n.val = 2202) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2202 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2203 (n : Fin 5011) (hn : n.val = 2203) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2203 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2204 (n : Fin 5011) (hn : n.val = 2204) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2204 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2205 (n : Fin 5011) (hn : n.val = 2205) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2205 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2206 (n : Fin 5011) (hn : n.val = 2206) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2206 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2207 (n : Fin 5011) (hn : n.val = 2207) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2207 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2208 (n : Fin 5011) (hn : n.val = 2208) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2208 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2209 (n : Fin 5011) (hn : n.val = 2209) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2209 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2210 (n : Fin 5011) (hn : n.val = 2210) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2210 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2211 (n : Fin 5011) (hn : n.val = 2211) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2211 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2212 (n : Fin 5011) (hn : n.val = 2212) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2212 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2213 (n : Fin 5011) (hn : n.val = 2213) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2213 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2214 (n : Fin 5011) (hn : n.val = 2214) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2214 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2215 (n : Fin 5011) (hn : n.val = 2215) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2215 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2216 (n : Fin 5011) (hn : n.val = 2216) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2216 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2217 (n : Fin 5011) (hn : n.val = 2217) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2217 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2218 (n : Fin 5011) (hn : n.val = 2218) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2218 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2219 (n : Fin 5011) (hn : n.val = 2219) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2219 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2220 (n : Fin 5011) (hn : n.val = 2220) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2220 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2221 (n : Fin 5011) (hn : n.val = 2221) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2221 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2222 (n : Fin 5011) (hn : n.val = 2222) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2222 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2223 (n : Fin 5011) (hn : n.val = 2223) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2223 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2224 (n : Fin 5011) (hn : n.val = 2224) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2224 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2225 (n : Fin 5011) (hn : n.val = 2225) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2225 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2226 (n : Fin 5011) (hn : n.val = 2226) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2226 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2227 (n : Fin 5011) (hn : n.val = 2227) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2227 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2228 (n : Fin 5011) (hn : n.val = 2228) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2228 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2229 (n : Fin 5011) (hn : n.val = 2229) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2229 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2230 (n : Fin 5011) (hn : n.val = 2230) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2230 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2231 (n : Fin 5011) (hn : n.val = 2231) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2231 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2232 (n : Fin 5011) (hn : n.val = 2232) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2232 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2233 (n : Fin 5011) (hn : n.val = 2233) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2233 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2234 (n : Fin 5011) (hn : n.val = 2234) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2234 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2235 (n : Fin 5011) (hn : n.val = 2235) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2235 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2236 (n : Fin 5011) (hn : n.val = 2236) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2236 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2237 (n : Fin 5011) (hn : n.val = 2237) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2237 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2238 (n : Fin 5011) (hn : n.val = 2238) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2238 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2239 (n : Fin 5011) (hn : n.val = 2239) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2239 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2240 (n : Fin 5011) (hn : n.val = 2240) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2240 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2241 (n : Fin 5011) (hn : n.val = 2241) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2241 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2242 (n : Fin 5011) (hn : n.val = 2242) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2242 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2243 (n : Fin 5011) (hn : n.val = 2243) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2243 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2244 (n : Fin 5011) (hn : n.val = 2244) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2244 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2245 (n : Fin 5011) (hn : n.val = 2245) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2245 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2246 (n : Fin 5011) (hn : n.val = 2246) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2246 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2247 (n : Fin 5011) (hn : n.val = 2247) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2247 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2248 (n : Fin 5011) (hn : n.val = 2248) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2248 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2249 (n : Fin 5011) (hn : n.val = 2249) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2249 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2250 (n : Fin 5011) (hn : n.val = 2250) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2250 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2251 (n : Fin 5011) (hn : n.val = 2251) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2251 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2252 (n : Fin 5011) (hn : n.val = 2252) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2252 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2253 (n : Fin 5011) (hn : n.val = 2253) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2253 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2254 (n : Fin 5011) (hn : n.val = 2254) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2254 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2255 (n : Fin 5011) (hn : n.val = 2255) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2255 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2256 (n : Fin 5011) (hn : n.val = 2256) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2256 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2257 (n : Fin 5011) (hn : n.val = 2257) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2257 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2258 (n : Fin 5011) (hn : n.val = 2258) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2258 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2259 (n : Fin 5011) (hn : n.val = 2259) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2259 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2260 (n : Fin 5011) (hn : n.val = 2260) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2260 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2261 (n : Fin 5011) (hn : n.val = 2261) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2261 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2262 (n : Fin 5011) (hn : n.val = 2262) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2262 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2263 (n : Fin 5011) (hn : n.val = 2263) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2263 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2264 (n : Fin 5011) (hn : n.val = 2264) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2264 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2265 (n : Fin 5011) (hn : n.val = 2265) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2265 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2266 (n : Fin 5011) (hn : n.val = 2266) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2266 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2267 (n : Fin 5011) (hn : n.val = 2267) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2267 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2268 (n : Fin 5011) (hn : n.val = 2268) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2268 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2269 (n : Fin 5011) (hn : n.val = 2269) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2269 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2270 (n : Fin 5011) (hn : n.val = 2270) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2270 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2271 (n : Fin 5011) (hn : n.val = 2271) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2271 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2272 (n : Fin 5011) (hn : n.val = 2272) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2272 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2273 (n : Fin 5011) (hn : n.val = 2273) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2273 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2274 (n : Fin 5011) (hn : n.val = 2274) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2274 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2275 (n : Fin 5011) (hn : n.val = 2275) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2275 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2276 (n : Fin 5011) (hn : n.val = 2276) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2276 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2277 (n : Fin 5011) (hn : n.val = 2277) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2277 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2278 (n : Fin 5011) (hn : n.val = 2278) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2278 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2279 (n : Fin 5011) (hn : n.val = 2279) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2279 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2280 (n : Fin 5011) (hn : n.val = 2280) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2280 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2281 (n : Fin 5011) (hn : n.val = 2281) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2281 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2282 (n : Fin 5011) (hn : n.val = 2282) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2282 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2283 (n : Fin 5011) (hn : n.val = 2283) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2283 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2284 (n : Fin 5011) (hn : n.val = 2284) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2284 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2285 (n : Fin 5011) (hn : n.val = 2285) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2285 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2286 (n : Fin 5011) (hn : n.val = 2286) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2286 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2287 (n : Fin 5011) (hn : n.val = 2287) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2287 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2288 (n : Fin 5011) (hn : n.val = 2288) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2288 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2289 (n : Fin 5011) (hn : n.val = 2289) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2289 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2290 (n : Fin 5011) (hn : n.val = 2290) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2290 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2291 (n : Fin 5011) (hn : n.val = 2291) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2291 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2292 (n : Fin 5011) (hn : n.val = 2292) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2292 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2293 (n : Fin 5011) (hn : n.val = 2293) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2293 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2294 (n : Fin 5011) (hn : n.val = 2294) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2294 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2295 (n : Fin 5011) (hn : n.val = 2295) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2295 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2296 (n : Fin 5011) (hn : n.val = 2296) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2296 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2297 (n : Fin 5011) (hn : n.val = 2297) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2297 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2298 (n : Fin 5011) (hn : n.val = 2298) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2298 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2299 (n : Fin 5011) (hn : n.val = 2299) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2299 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2600 (n : Fin 5011) (hn : n.val = 2600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2600 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2601 (n : Fin 5011) (hn : n.val = 2601) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2601 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2602 (n : Fin 5011) (hn : n.val = 2602) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2602 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2603 (n : Fin 5011) (hn : n.val = 2603) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2603 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2604 (n : Fin 5011) (hn : n.val = 2604) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2604 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2605 (n : Fin 5011) (hn : n.val = 2605) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2605 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2606 (n : Fin 5011) (hn : n.val = 2606) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2606 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2607 (n : Fin 5011) (hn : n.val = 2607) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2607 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2608 (n : Fin 5011) (hn : n.val = 2608) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2608 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2609 (n : Fin 5011) (hn : n.val = 2609) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2609 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2610 (n : Fin 5011) (hn : n.val = 2610) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2610 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2611 (n : Fin 5011) (hn : n.val = 2611) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2611 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2612 (n : Fin 5011) (hn : n.val = 2612) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2612 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2613 (n : Fin 5011) (hn : n.val = 2613) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2613 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2614 (n : Fin 5011) (hn : n.val = 2614) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2614 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2615 (n : Fin 5011) (hn : n.val = 2615) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2615 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2616 (n : Fin 5011) (hn : n.val = 2616) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2616 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2617 (n : Fin 5011) (hn : n.val = 2617) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2617 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2618 (n : Fin 5011) (hn : n.val = 2618) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2618 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2619 (n : Fin 5011) (hn : n.val = 2619) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2619 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2620 (n : Fin 5011) (hn : n.val = 2620) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2620 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2621 (n : Fin 5011) (hn : n.val = 2621) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2621 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2622 (n : Fin 5011) (hn : n.val = 2622) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2622 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2623 (n : Fin 5011) (hn : n.val = 2623) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2623 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2624 (n : Fin 5011) (hn : n.val = 2624) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2624 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2625 (n : Fin 5011) (hn : n.val = 2625) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2625 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2626 (n : Fin 5011) (hn : n.val = 2626) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2626 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2627 (n : Fin 5011) (hn : n.val = 2627) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2627 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2628 (n : Fin 5011) (hn : n.val = 2628) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2628 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2629 (n : Fin 5011) (hn : n.val = 2629) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2629 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2630 (n : Fin 5011) (hn : n.val = 2630) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2630 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2631 (n : Fin 5011) (hn : n.val = 2631) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2631 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2632 (n : Fin 5011) (hn : n.val = 2632) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2632 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2633 (n : Fin 5011) (hn : n.val = 2633) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2633 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2634 (n : Fin 5011) (hn : n.val = 2634) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2634 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2635 (n : Fin 5011) (hn : n.val = 2635) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2635 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2636 (n : Fin 5011) (hn : n.val = 2636) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2636 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2637 (n : Fin 5011) (hn : n.val = 2637) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2637 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2638 (n : Fin 5011) (hn : n.val = 2638) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2638 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2639 (n : Fin 5011) (hn : n.val = 2639) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2639 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2640 (n : Fin 5011) (hn : n.val = 2640) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2640 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2641 (n : Fin 5011) (hn : n.val = 2641) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2641 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2642 (n : Fin 5011) (hn : n.val = 2642) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2642 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2643 (n : Fin 5011) (hn : n.val = 2643) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2643 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2644 (n : Fin 5011) (hn : n.val = 2644) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2644 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2645 (n : Fin 5011) (hn : n.val = 2645) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2645 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2646 (n : Fin 5011) (hn : n.val = 2646) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2646 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2647 (n : Fin 5011) (hn : n.val = 2647) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2647 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2648 (n : Fin 5011) (hn : n.val = 2648) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2648 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2649 (n : Fin 5011) (hn : n.val = 2649) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2649 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2650 (n : Fin 5011) (hn : n.val = 2650) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2650 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2651 (n : Fin 5011) (hn : n.val = 2651) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2651 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2652 (n : Fin 5011) (hn : n.val = 2652) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2652 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2653 (n : Fin 5011) (hn : n.val = 2653) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2653 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2654 (n : Fin 5011) (hn : n.val = 2654) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2654 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2655 (n : Fin 5011) (hn : n.val = 2655) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2655 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2656 (n : Fin 5011) (hn : n.val = 2656) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2656 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2657 (n : Fin 5011) (hn : n.val = 2657) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2657 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2658 (n : Fin 5011) (hn : n.val = 2658) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2658 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2659 (n : Fin 5011) (hn : n.val = 2659) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2659 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2660 (n : Fin 5011) (hn : n.val = 2660) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2660 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2661 (n : Fin 5011) (hn : n.val = 2661) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2661 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2662 (n : Fin 5011) (hn : n.val = 2662) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2662 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2663 (n : Fin 5011) (hn : n.val = 2663) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2663 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2664 (n : Fin 5011) (hn : n.val = 2664) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2664 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2665 (n : Fin 5011) (hn : n.val = 2665) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2665 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2666 (n : Fin 5011) (hn : n.val = 2666) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2666 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2667 (n : Fin 5011) (hn : n.val = 2667) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2667 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2668 (n : Fin 5011) (hn : n.val = 2668) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2668 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2669 (n : Fin 5011) (hn : n.val = 2669) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2669 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2670 (n : Fin 5011) (hn : n.val = 2670) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2670 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2671 (n : Fin 5011) (hn : n.val = 2671) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2671 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2672 (n : Fin 5011) (hn : n.val = 2672) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2672 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2673 (n : Fin 5011) (hn : n.val = 2673) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2673 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2674 (n : Fin 5011) (hn : n.val = 2674) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2674 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2675 (n : Fin 5011) (hn : n.val = 2675) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2675 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2676 (n : Fin 5011) (hn : n.val = 2676) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2676 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2677 (n : Fin 5011) (hn : n.val = 2677) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2677 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2678 (n : Fin 5011) (hn : n.val = 2678) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2678 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2679 (n : Fin 5011) (hn : n.val = 2679) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2679 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2680 (n : Fin 5011) (hn : n.val = 2680) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2680 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2681 (n : Fin 5011) (hn : n.val = 2681) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2681 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2682 (n : Fin 5011) (hn : n.val = 2682) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2682 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2683 (n : Fin 5011) (hn : n.val = 2683) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2683 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2684 (n : Fin 5011) (hn : n.val = 2684) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2684 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2685 (n : Fin 5011) (hn : n.val = 2685) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2685 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2686 (n : Fin 5011) (hn : n.val = 2686) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2686 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2687 (n : Fin 5011) (hn : n.val = 2687) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2687 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2688 (n : Fin 5011) (hn : n.val = 2688) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2688 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2689 (n : Fin 5011) (hn : n.val = 2689) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2689 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2690 (n : Fin 5011) (hn : n.val = 2690) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2690 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2691 (n : Fin 5011) (hn : n.val = 2691) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2691 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2692 (n : Fin 5011) (hn : n.val = 2692) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2692 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2693 (n : Fin 5011) (hn : n.val = 2693) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2693 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2694 (n : Fin 5011) (hn : n.val = 2694) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2694 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2695 (n : Fin 5011) (hn : n.val = 2695) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2695 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2696 (n : Fin 5011) (hn : n.val = 2696) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2696 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2697 (n : Fin 5011) (hn : n.val = 2697) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2697 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2698 (n : Fin 5011) (hn : n.val = 2698) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2698 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_2699 (n : Fin 5011) (hn : n.val = 2699) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 2699 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3000 (n : Fin 5011) (hn : n.val = 3000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3000 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3001 (n : Fin 5011) (hn : n.val = 3001) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3001 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3002 (n : Fin 5011) (hn : n.val = 3002) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3002 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3003 (n : Fin 5011) (hn : n.val = 3003) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3003 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3004 (n : Fin 5011) (hn : n.val = 3004) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3004 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3005 (n : Fin 5011) (hn : n.val = 3005) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3005 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3006 (n : Fin 5011) (hn : n.val = 3006) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3006 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3007 (n : Fin 5011) (hn : n.val = 3007) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3007 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3008 (n : Fin 5011) (hn : n.val = 3008) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3008 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3009 (n : Fin 5011) (hn : n.val = 3009) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3009 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3010 (n : Fin 5011) (hn : n.val = 3010) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3010 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3011 (n : Fin 5011) (hn : n.val = 3011) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3011 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3012 (n : Fin 5011) (hn : n.val = 3012) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3012 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3013 (n : Fin 5011) (hn : n.val = 3013) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3013 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3014 (n : Fin 5011) (hn : n.val = 3014) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3014 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3015 (n : Fin 5011) (hn : n.val = 3015) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3015 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3016 (n : Fin 5011) (hn : n.val = 3016) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3016 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3017 (n : Fin 5011) (hn : n.val = 3017) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3017 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3018 (n : Fin 5011) (hn : n.val = 3018) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3018 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3019 (n : Fin 5011) (hn : n.val = 3019) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3019 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3020 (n : Fin 5011) (hn : n.val = 3020) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3020 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3021 (n : Fin 5011) (hn : n.val = 3021) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3021 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3022 (n : Fin 5011) (hn : n.val = 3022) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3022 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3023 (n : Fin 5011) (hn : n.val = 3023) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3023 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3024 (n : Fin 5011) (hn : n.val = 3024) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3024 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3025 (n : Fin 5011) (hn : n.val = 3025) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3025 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3026 (n : Fin 5011) (hn : n.val = 3026) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3026 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3027 (n : Fin 5011) (hn : n.val = 3027) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3027 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3028 (n : Fin 5011) (hn : n.val = 3028) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3028 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3029 (n : Fin 5011) (hn : n.val = 3029) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3029 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3030 (n : Fin 5011) (hn : n.val = 3030) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3030 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3031 (n : Fin 5011) (hn : n.val = 3031) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3031 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3032 (n : Fin 5011) (hn : n.val = 3032) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3032 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3033 (n : Fin 5011) (hn : n.val = 3033) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3033 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3034 (n : Fin 5011) (hn : n.val = 3034) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3034 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3035 (n : Fin 5011) (hn : n.val = 3035) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3035 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3036 (n : Fin 5011) (hn : n.val = 3036) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3036 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3037 (n : Fin 5011) (hn : n.val = 3037) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3037 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3038 (n : Fin 5011) (hn : n.val = 3038) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3038 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3039 (n : Fin 5011) (hn : n.val = 3039) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3039 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3040 (n : Fin 5011) (hn : n.val = 3040) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3040 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3041 (n : Fin 5011) (hn : n.val = 3041) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3041 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3042 (n : Fin 5011) (hn : n.val = 3042) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3042 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3043 (n : Fin 5011) (hn : n.val = 3043) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3043 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3044 (n : Fin 5011) (hn : n.val = 3044) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3044 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3045 (n : Fin 5011) (hn : n.val = 3045) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3045 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3046 (n : Fin 5011) (hn : n.val = 3046) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3046 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3047 (n : Fin 5011) (hn : n.val = 3047) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3047 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3048 (n : Fin 5011) (hn : n.val = 3048) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3048 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3049 (n : Fin 5011) (hn : n.val = 3049) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3049 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3050 (n : Fin 5011) (hn : n.val = 3050) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3050 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3051 (n : Fin 5011) (hn : n.val = 3051) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3051 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3052 (n : Fin 5011) (hn : n.val = 3052) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3052 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3053 (n : Fin 5011) (hn : n.val = 3053) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3053 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3054 (n : Fin 5011) (hn : n.val = 3054) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3054 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3055 (n : Fin 5011) (hn : n.val = 3055) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3055 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3056 (n : Fin 5011) (hn : n.val = 3056) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3056 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3057 (n : Fin 5011) (hn : n.val = 3057) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3057 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3058 (n : Fin 5011) (hn : n.val = 3058) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3058 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3059 (n : Fin 5011) (hn : n.val = 3059) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3059 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3060 (n : Fin 5011) (hn : n.val = 3060) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3060 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3061 (n : Fin 5011) (hn : n.val = 3061) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3061 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3062 (n : Fin 5011) (hn : n.val = 3062) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3062 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3063 (n : Fin 5011) (hn : n.val = 3063) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3063 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3064 (n : Fin 5011) (hn : n.val = 3064) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3064 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3065 (n : Fin 5011) (hn : n.val = 3065) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3065 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3066 (n : Fin 5011) (hn : n.val = 3066) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3066 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3067 (n : Fin 5011) (hn : n.val = 3067) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3067 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3068 (n : Fin 5011) (hn : n.val = 3068) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3068 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3069 (n : Fin 5011) (hn : n.val = 3069) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3069 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3070 (n : Fin 5011) (hn : n.val = 3070) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3070 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3071 (n : Fin 5011) (hn : n.val = 3071) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3071 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3072 (n : Fin 5011) (hn : n.val = 3072) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3072 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3073 (n : Fin 5011) (hn : n.val = 3073) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3073 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3074 (n : Fin 5011) (hn : n.val = 3074) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3074 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3075 (n : Fin 5011) (hn : n.val = 3075) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3075 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3076 (n : Fin 5011) (hn : n.val = 3076) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3076 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3077 (n : Fin 5011) (hn : n.val = 3077) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3077 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3078 (n : Fin 5011) (hn : n.val = 3078) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3078 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3079 (n : Fin 5011) (hn : n.val = 3079) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3079 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3080 (n : Fin 5011) (hn : n.val = 3080) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3080 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3081 (n : Fin 5011) (hn : n.val = 3081) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3081 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3082 (n : Fin 5011) (hn : n.val = 3082) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3082 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3083 (n : Fin 5011) (hn : n.val = 3083) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3083 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3084 (n : Fin 5011) (hn : n.val = 3084) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3084 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3085 (n : Fin 5011) (hn : n.val = 3085) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3085 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3086 (n : Fin 5011) (hn : n.val = 3086) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3086 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3087 (n : Fin 5011) (hn : n.val = 3087) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3087 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3088 (n : Fin 5011) (hn : n.val = 3088) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3088 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3089 (n : Fin 5011) (hn : n.val = 3089) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3089 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3090 (n : Fin 5011) (hn : n.val = 3090) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3090 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3091 (n : Fin 5011) (hn : n.val = 3091) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3091 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3092 (n : Fin 5011) (hn : n.val = 3092) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3092 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3093 (n : Fin 5011) (hn : n.val = 3093) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3093 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3094 (n : Fin 5011) (hn : n.val = 3094) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3094 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3095 (n : Fin 5011) (hn : n.val = 3095) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3095 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3096 (n : Fin 5011) (hn : n.val = 3096) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3096 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3097 (n : Fin 5011) (hn : n.val = 3097) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3097 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3098 (n : Fin 5011) (hn : n.val = 3098) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3098 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3099 (n : Fin 5011) (hn : n.val = 3099) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3099 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3400 (n : Fin 5011) (hn : n.val = 3400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3400 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3401 (n : Fin 5011) (hn : n.val = 3401) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3401 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3402 (n : Fin 5011) (hn : n.val = 3402) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3402 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3403 (n : Fin 5011) (hn : n.val = 3403) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3403 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3404 (n : Fin 5011) (hn : n.val = 3404) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3404 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3405 (n : Fin 5011) (hn : n.val = 3405) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3405 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3406 (n : Fin 5011) (hn : n.val = 3406) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3406 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3407 (n : Fin 5011) (hn : n.val = 3407) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3407 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3408 (n : Fin 5011) (hn : n.val = 3408) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3408 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3409 (n : Fin 5011) (hn : n.val = 3409) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3409 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3410 (n : Fin 5011) (hn : n.val = 3410) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3410 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3411 (n : Fin 5011) (hn : n.val = 3411) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3411 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3412 (n : Fin 5011) (hn : n.val = 3412) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3412 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3413 (n : Fin 5011) (hn : n.val = 3413) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3413 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3414 (n : Fin 5011) (hn : n.val = 3414) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3414 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3415 (n : Fin 5011) (hn : n.val = 3415) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3415 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3416 (n : Fin 5011) (hn : n.val = 3416) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3416 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3417 (n : Fin 5011) (hn : n.val = 3417) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3417 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3418 (n : Fin 5011) (hn : n.val = 3418) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3418 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3419 (n : Fin 5011) (hn : n.val = 3419) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3419 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3420 (n : Fin 5011) (hn : n.val = 3420) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3420 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3421 (n : Fin 5011) (hn : n.val = 3421) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3421 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3422 (n : Fin 5011) (hn : n.val = 3422) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3422 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3423 (n : Fin 5011) (hn : n.val = 3423) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3423 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3424 (n : Fin 5011) (hn : n.val = 3424) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3424 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3425 (n : Fin 5011) (hn : n.val = 3425) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3425 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3426 (n : Fin 5011) (hn : n.val = 3426) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3426 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3427 (n : Fin 5011) (hn : n.val = 3427) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3427 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3428 (n : Fin 5011) (hn : n.val = 3428) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3428 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3429 (n : Fin 5011) (hn : n.val = 3429) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3429 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3430 (n : Fin 5011) (hn : n.val = 3430) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3430 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3431 (n : Fin 5011) (hn : n.val = 3431) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3431 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3432 (n : Fin 5011) (hn : n.val = 3432) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3432 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3433 (n : Fin 5011) (hn : n.val = 3433) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3433 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3434 (n : Fin 5011) (hn : n.val = 3434) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3434 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3435 (n : Fin 5011) (hn : n.val = 3435) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3435 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3436 (n : Fin 5011) (hn : n.val = 3436) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3436 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3437 (n : Fin 5011) (hn : n.val = 3437) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3437 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3438 (n : Fin 5011) (hn : n.val = 3438) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3438 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3439 (n : Fin 5011) (hn : n.val = 3439) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3439 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3440 (n : Fin 5011) (hn : n.val = 3440) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3440 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3441 (n : Fin 5011) (hn : n.val = 3441) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3441 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3442 (n : Fin 5011) (hn : n.val = 3442) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3442 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3443 (n : Fin 5011) (hn : n.val = 3443) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3443 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3444 (n : Fin 5011) (hn : n.val = 3444) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3444 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3445 (n : Fin 5011) (hn : n.val = 3445) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3445 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3446 (n : Fin 5011) (hn : n.val = 3446) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3446 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3447 (n : Fin 5011) (hn : n.val = 3447) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3447 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3448 (n : Fin 5011) (hn : n.val = 3448) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3448 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3449 (n : Fin 5011) (hn : n.val = 3449) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3449 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3450 (n : Fin 5011) (hn : n.val = 3450) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3450 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3451 (n : Fin 5011) (hn : n.val = 3451) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3451 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3452 (n : Fin 5011) (hn : n.val = 3452) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3452 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3453 (n : Fin 5011) (hn : n.val = 3453) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3453 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3454 (n : Fin 5011) (hn : n.val = 3454) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3454 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3455 (n : Fin 5011) (hn : n.val = 3455) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3455 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3456 (n : Fin 5011) (hn : n.val = 3456) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3456 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3457 (n : Fin 5011) (hn : n.val = 3457) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3457 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3458 (n : Fin 5011) (hn : n.val = 3458) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3458 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3459 (n : Fin 5011) (hn : n.val = 3459) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3459 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3460 (n : Fin 5011) (hn : n.val = 3460) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3460 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3461 (n : Fin 5011) (hn : n.val = 3461) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3461 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3462 (n : Fin 5011) (hn : n.val = 3462) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3462 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3463 (n : Fin 5011) (hn : n.val = 3463) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3463 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3464 (n : Fin 5011) (hn : n.val = 3464) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3464 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3465 (n : Fin 5011) (hn : n.val = 3465) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3465 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3466 (n : Fin 5011) (hn : n.val = 3466) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3466 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3467 (n : Fin 5011) (hn : n.val = 3467) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3467 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3468 (n : Fin 5011) (hn : n.val = 3468) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3468 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3469 (n : Fin 5011) (hn : n.val = 3469) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3469 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3470 (n : Fin 5011) (hn : n.val = 3470) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3470 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3471 (n : Fin 5011) (hn : n.val = 3471) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3471 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3472 (n : Fin 5011) (hn : n.val = 3472) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3472 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3473 (n : Fin 5011) (hn : n.val = 3473) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3473 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3474 (n : Fin 5011) (hn : n.val = 3474) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3474 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3475 (n : Fin 5011) (hn : n.val = 3475) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3475 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3476 (n : Fin 5011) (hn : n.val = 3476) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3476 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3477 (n : Fin 5011) (hn : n.val = 3477) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3477 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3478 (n : Fin 5011) (hn : n.val = 3478) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3478 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3479 (n : Fin 5011) (hn : n.val = 3479) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3479 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3480 (n : Fin 5011) (hn : n.val = 3480) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3480 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3481 (n : Fin 5011) (hn : n.val = 3481) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3481 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3482 (n : Fin 5011) (hn : n.val = 3482) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3482 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3483 (n : Fin 5011) (hn : n.val = 3483) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3483 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3484 (n : Fin 5011) (hn : n.val = 3484) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3484 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3485 (n : Fin 5011) (hn : n.val = 3485) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3485 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3486 (n : Fin 5011) (hn : n.val = 3486) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3486 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3487 (n : Fin 5011) (hn : n.val = 3487) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3487 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3488 (n : Fin 5011) (hn : n.val = 3488) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3488 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3489 (n : Fin 5011) (hn : n.val = 3489) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3489 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3490 (n : Fin 5011) (hn : n.val = 3490) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3490 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3491 (n : Fin 5011) (hn : n.val = 3491) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3491 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3492 (n : Fin 5011) (hn : n.val = 3492) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3492 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3493 (n : Fin 5011) (hn : n.val = 3493) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3493 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3494 (n : Fin 5011) (hn : n.val = 3494) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3494 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3495 (n : Fin 5011) (hn : n.val = 3495) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3495 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3496 (n : Fin 5011) (hn : n.val = 3496) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3496 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3497 (n : Fin 5011) (hn : n.val = 3497) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3497 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3498 (n : Fin 5011) (hn : n.val = 3498) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3498 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3499 (n : Fin 5011) (hn : n.val = 3499) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3499 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3800 (n : Fin 5011) (hn : n.val = 3800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3800 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3801 (n : Fin 5011) (hn : n.val = 3801) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3801 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3802 (n : Fin 5011) (hn : n.val = 3802) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3802 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3803 (n : Fin 5011) (hn : n.val = 3803) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3803 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3804 (n : Fin 5011) (hn : n.val = 3804) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3804 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3805 (n : Fin 5011) (hn : n.val = 3805) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3805 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3806 (n : Fin 5011) (hn : n.val = 3806) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3806 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3807 (n : Fin 5011) (hn : n.val = 3807) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3807 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3808 (n : Fin 5011) (hn : n.val = 3808) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3808 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3809 (n : Fin 5011) (hn : n.val = 3809) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3809 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3810 (n : Fin 5011) (hn : n.val = 3810) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3810 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3811 (n : Fin 5011) (hn : n.val = 3811) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3811 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3812 (n : Fin 5011) (hn : n.val = 3812) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3812 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3813 (n : Fin 5011) (hn : n.val = 3813) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3813 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3814 (n : Fin 5011) (hn : n.val = 3814) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3814 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3815 (n : Fin 5011) (hn : n.val = 3815) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3815 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3816 (n : Fin 5011) (hn : n.val = 3816) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3816 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3817 (n : Fin 5011) (hn : n.val = 3817) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3817 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3818 (n : Fin 5011) (hn : n.val = 3818) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3818 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3819 (n : Fin 5011) (hn : n.val = 3819) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3819 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3820 (n : Fin 5011) (hn : n.val = 3820) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3820 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3821 (n : Fin 5011) (hn : n.val = 3821) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3821 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3822 (n : Fin 5011) (hn : n.val = 3822) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3822 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3823 (n : Fin 5011) (hn : n.val = 3823) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3823 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3824 (n : Fin 5011) (hn : n.val = 3824) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3824 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3825 (n : Fin 5011) (hn : n.val = 3825) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3825 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3826 (n : Fin 5011) (hn : n.val = 3826) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3826 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3827 (n : Fin 5011) (hn : n.val = 3827) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3827 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3828 (n : Fin 5011) (hn : n.val = 3828) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3828 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3829 (n : Fin 5011) (hn : n.val = 3829) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3829 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3830 (n : Fin 5011) (hn : n.val = 3830) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3830 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3831 (n : Fin 5011) (hn : n.val = 3831) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3831 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3832 (n : Fin 5011) (hn : n.val = 3832) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3832 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3833 (n : Fin 5011) (hn : n.val = 3833) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3833 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3834 (n : Fin 5011) (hn : n.val = 3834) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3834 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3835 (n : Fin 5011) (hn : n.val = 3835) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3835 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3836 (n : Fin 5011) (hn : n.val = 3836) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3836 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3837 (n : Fin 5011) (hn : n.val = 3837) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3837 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3838 (n : Fin 5011) (hn : n.val = 3838) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3838 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3839 (n : Fin 5011) (hn : n.val = 3839) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3839 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3840 (n : Fin 5011) (hn : n.val = 3840) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3840 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3841 (n : Fin 5011) (hn : n.val = 3841) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3841 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3842 (n : Fin 5011) (hn : n.val = 3842) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3842 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3843 (n : Fin 5011) (hn : n.val = 3843) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3843 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3844 (n : Fin 5011) (hn : n.val = 3844) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3844 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3845 (n : Fin 5011) (hn : n.val = 3845) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3845 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3846 (n : Fin 5011) (hn : n.val = 3846) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3846 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3847 (n : Fin 5011) (hn : n.val = 3847) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3847 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3848 (n : Fin 5011) (hn : n.val = 3848) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3848 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3849 (n : Fin 5011) (hn : n.val = 3849) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3849 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3850 (n : Fin 5011) (hn : n.val = 3850) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3850 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3851 (n : Fin 5011) (hn : n.val = 3851) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3851 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3852 (n : Fin 5011) (hn : n.val = 3852) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3852 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3853 (n : Fin 5011) (hn : n.val = 3853) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3853 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3854 (n : Fin 5011) (hn : n.val = 3854) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3854 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3855 (n : Fin 5011) (hn : n.val = 3855) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3855 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3856 (n : Fin 5011) (hn : n.val = 3856) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3856 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3857 (n : Fin 5011) (hn : n.val = 3857) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3857 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3858 (n : Fin 5011) (hn : n.val = 3858) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3858 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3859 (n : Fin 5011) (hn : n.val = 3859) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3859 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3860 (n : Fin 5011) (hn : n.val = 3860) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3860 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3861 (n : Fin 5011) (hn : n.val = 3861) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3861 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3862 (n : Fin 5011) (hn : n.val = 3862) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3862 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3863 (n : Fin 5011) (hn : n.val = 3863) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3863 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3864 (n : Fin 5011) (hn : n.val = 3864) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3864 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3865 (n : Fin 5011) (hn : n.val = 3865) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3865 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3866 (n : Fin 5011) (hn : n.val = 3866) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3866 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3867 (n : Fin 5011) (hn : n.val = 3867) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3867 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3868 (n : Fin 5011) (hn : n.val = 3868) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3868 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3869 (n : Fin 5011) (hn : n.val = 3869) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3869 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3870 (n : Fin 5011) (hn : n.val = 3870) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3870 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3871 (n : Fin 5011) (hn : n.val = 3871) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3871 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3872 (n : Fin 5011) (hn : n.val = 3872) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3872 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3873 (n : Fin 5011) (hn : n.val = 3873) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3873 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3874 (n : Fin 5011) (hn : n.val = 3874) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3874 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3875 (n : Fin 5011) (hn : n.val = 3875) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3875 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3876 (n : Fin 5011) (hn : n.val = 3876) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3876 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3877 (n : Fin 5011) (hn : n.val = 3877) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3877 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3878 (n : Fin 5011) (hn : n.val = 3878) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3878 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3879 (n : Fin 5011) (hn : n.val = 3879) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3879 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3880 (n : Fin 5011) (hn : n.val = 3880) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3880 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3881 (n : Fin 5011) (hn : n.val = 3881) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3881 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3882 (n : Fin 5011) (hn : n.val = 3882) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3882 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3883 (n : Fin 5011) (hn : n.val = 3883) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3883 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3884 (n : Fin 5011) (hn : n.val = 3884) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3884 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3885 (n : Fin 5011) (hn : n.val = 3885) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3885 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3886 (n : Fin 5011) (hn : n.val = 3886) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3886 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3887 (n : Fin 5011) (hn : n.val = 3887) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3887 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3888 (n : Fin 5011) (hn : n.val = 3888) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3888 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3889 (n : Fin 5011) (hn : n.val = 3889) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3889 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3890 (n : Fin 5011) (hn : n.val = 3890) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3890 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3891 (n : Fin 5011) (hn : n.val = 3891) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3891 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3892 (n : Fin 5011) (hn : n.val = 3892) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3892 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3893 (n : Fin 5011) (hn : n.val = 3893) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3893 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3894 (n : Fin 5011) (hn : n.val = 3894) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3894 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3895 (n : Fin 5011) (hn : n.val = 3895) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3895 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3896 (n : Fin 5011) (hn : n.val = 3896) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3896 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3897 (n : Fin 5011) (hn : n.val = 3897) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3897 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3898 (n : Fin 5011) (hn : n.val = 3898) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3898 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_3899 (n : Fin 5011) (hn : n.val = 3899) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 3899 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4200 (n : Fin 5011) (hn : n.val = 4200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4200 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4201 (n : Fin 5011) (hn : n.val = 4201) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4201 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4202 (n : Fin 5011) (hn : n.val = 4202) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4202 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4203 (n : Fin 5011) (hn : n.val = 4203) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4203 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4204 (n : Fin 5011) (hn : n.val = 4204) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4204 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4205 (n : Fin 5011) (hn : n.val = 4205) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4205 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4206 (n : Fin 5011) (hn : n.val = 4206) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4206 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4207 (n : Fin 5011) (hn : n.val = 4207) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4207 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4208 (n : Fin 5011) (hn : n.val = 4208) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4208 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4209 (n : Fin 5011) (hn : n.val = 4209) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4209 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4210 (n : Fin 5011) (hn : n.val = 4210) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4210 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4211 (n : Fin 5011) (hn : n.val = 4211) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4211 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4212 (n : Fin 5011) (hn : n.val = 4212) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4212 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4213 (n : Fin 5011) (hn : n.val = 4213) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4213 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4214 (n : Fin 5011) (hn : n.val = 4214) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4214 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4215 (n : Fin 5011) (hn : n.val = 4215) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4215 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4216 (n : Fin 5011) (hn : n.val = 4216) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4216 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4217 (n : Fin 5011) (hn : n.val = 4217) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4217 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4218 (n : Fin 5011) (hn : n.val = 4218) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4218 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4219 (n : Fin 5011) (hn : n.val = 4219) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4219 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4220 (n : Fin 5011) (hn : n.val = 4220) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4220 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4221 (n : Fin 5011) (hn : n.val = 4221) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4221 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4222 (n : Fin 5011) (hn : n.val = 4222) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4222 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4223 (n : Fin 5011) (hn : n.val = 4223) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4223 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4224 (n : Fin 5011) (hn : n.val = 4224) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4224 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4225 (n : Fin 5011) (hn : n.val = 4225) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4225 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4226 (n : Fin 5011) (hn : n.val = 4226) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4226 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4227 (n : Fin 5011) (hn : n.val = 4227) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4227 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4228 (n : Fin 5011) (hn : n.val = 4228) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4228 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4229 (n : Fin 5011) (hn : n.val = 4229) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4229 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4230 (n : Fin 5011) (hn : n.val = 4230) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4230 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4231 (n : Fin 5011) (hn : n.val = 4231) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4231 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4232 (n : Fin 5011) (hn : n.val = 4232) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4232 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4233 (n : Fin 5011) (hn : n.val = 4233) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4233 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4234 (n : Fin 5011) (hn : n.val = 4234) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4234 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4235 (n : Fin 5011) (hn : n.val = 4235) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4235 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4236 (n : Fin 5011) (hn : n.val = 4236) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4236 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4237 (n : Fin 5011) (hn : n.val = 4237) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4237 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4238 (n : Fin 5011) (hn : n.val = 4238) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4238 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4239 (n : Fin 5011) (hn : n.val = 4239) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4239 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4240 (n : Fin 5011) (hn : n.val = 4240) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4240 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4241 (n : Fin 5011) (hn : n.val = 4241) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4241 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4242 (n : Fin 5011) (hn : n.val = 4242) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4242 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4243 (n : Fin 5011) (hn : n.val = 4243) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4243 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4244 (n : Fin 5011) (hn : n.val = 4244) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4244 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4245 (n : Fin 5011) (hn : n.val = 4245) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4245 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4246 (n : Fin 5011) (hn : n.val = 4246) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4246 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4247 (n : Fin 5011) (hn : n.val = 4247) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4247 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4248 (n : Fin 5011) (hn : n.val = 4248) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4248 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4249 (n : Fin 5011) (hn : n.val = 4249) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4249 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4250 (n : Fin 5011) (hn : n.val = 4250) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4250 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4251 (n : Fin 5011) (hn : n.val = 4251) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4251 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4252 (n : Fin 5011) (hn : n.val = 4252) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4252 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4253 (n : Fin 5011) (hn : n.val = 4253) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4253 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4254 (n : Fin 5011) (hn : n.val = 4254) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4254 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4255 (n : Fin 5011) (hn : n.val = 4255) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4255 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4256 (n : Fin 5011) (hn : n.val = 4256) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4256 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4257 (n : Fin 5011) (hn : n.val = 4257) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4257 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4258 (n : Fin 5011) (hn : n.val = 4258) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4258 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4259 (n : Fin 5011) (hn : n.val = 4259) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4259 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4260 (n : Fin 5011) (hn : n.val = 4260) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4260 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4261 (n : Fin 5011) (hn : n.val = 4261) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4261 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4262 (n : Fin 5011) (hn : n.val = 4262) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4262 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4263 (n : Fin 5011) (hn : n.val = 4263) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4263 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4264 (n : Fin 5011) (hn : n.val = 4264) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4264 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4265 (n : Fin 5011) (hn : n.val = 4265) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4265 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4266 (n : Fin 5011) (hn : n.val = 4266) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4266 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4267 (n : Fin 5011) (hn : n.val = 4267) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4267 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4268 (n : Fin 5011) (hn : n.val = 4268) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4268 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4269 (n : Fin 5011) (hn : n.val = 4269) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4269 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4270 (n : Fin 5011) (hn : n.val = 4270) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4270 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4271 (n : Fin 5011) (hn : n.val = 4271) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4271 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4272 (n : Fin 5011) (hn : n.val = 4272) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4272 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4273 (n : Fin 5011) (hn : n.val = 4273) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4273 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4274 (n : Fin 5011) (hn : n.val = 4274) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4274 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4275 (n : Fin 5011) (hn : n.val = 4275) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4275 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4276 (n : Fin 5011) (hn : n.val = 4276) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4276 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4277 (n : Fin 5011) (hn : n.val = 4277) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4277 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4278 (n : Fin 5011) (hn : n.val = 4278) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4278 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4279 (n : Fin 5011) (hn : n.val = 4279) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4279 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4280 (n : Fin 5011) (hn : n.val = 4280) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4280 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4281 (n : Fin 5011) (hn : n.val = 4281) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4281 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4282 (n : Fin 5011) (hn : n.val = 4282) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4282 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4283 (n : Fin 5011) (hn : n.val = 4283) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4283 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4284 (n : Fin 5011) (hn : n.val = 4284) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4284 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4285 (n : Fin 5011) (hn : n.val = 4285) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4285 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4286 (n : Fin 5011) (hn : n.val = 4286) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4286 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4287 (n : Fin 5011) (hn : n.val = 4287) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4287 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4288 (n : Fin 5011) (hn : n.val = 4288) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4288 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4289 (n : Fin 5011) (hn : n.val = 4289) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4289 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4290 (n : Fin 5011) (hn : n.val = 4290) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4290 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4291 (n : Fin 5011) (hn : n.val = 4291) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4291 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4292 (n : Fin 5011) (hn : n.val = 4292) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4292 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4293 (n : Fin 5011) (hn : n.val = 4293) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4293 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4294 (n : Fin 5011) (hn : n.val = 4294) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4294 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4295 (n : Fin 5011) (hn : n.val = 4295) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4295 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4296 (n : Fin 5011) (hn : n.val = 4296) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4296 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4297 (n : Fin 5011) (hn : n.val = 4297) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4297 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4298 (n : Fin 5011) (hn : n.val = 4298) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4298 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4299 (n : Fin 5011) (hn : n.val = 4299) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4299 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4600 (n : Fin 5011) (hn : n.val = 4600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4600 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4601 (n : Fin 5011) (hn : n.val = 4601) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4601 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4602 (n : Fin 5011) (hn : n.val = 4602) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4602 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4603 (n : Fin 5011) (hn : n.val = 4603) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4603 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4604 (n : Fin 5011) (hn : n.val = 4604) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4604 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4605 (n : Fin 5011) (hn : n.val = 4605) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4605 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4606 (n : Fin 5011) (hn : n.val = 4606) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4606 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4607 (n : Fin 5011) (hn : n.val = 4607) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4607 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4608 (n : Fin 5011) (hn : n.val = 4608) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4608 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4609 (n : Fin 5011) (hn : n.val = 4609) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4609 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4610 (n : Fin 5011) (hn : n.val = 4610) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4610 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4611 (n : Fin 5011) (hn : n.val = 4611) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4611 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4612 (n : Fin 5011) (hn : n.val = 4612) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4612 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4613 (n : Fin 5011) (hn : n.val = 4613) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4613 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4614 (n : Fin 5011) (hn : n.val = 4614) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4614 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4615 (n : Fin 5011) (hn : n.val = 4615) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4615 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4616 (n : Fin 5011) (hn : n.val = 4616) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4616 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4617 (n : Fin 5011) (hn : n.val = 4617) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4617 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4618 (n : Fin 5011) (hn : n.val = 4618) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4618 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4619 (n : Fin 5011) (hn : n.val = 4619) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4619 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4620 (n : Fin 5011) (hn : n.val = 4620) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4620 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4621 (n : Fin 5011) (hn : n.val = 4621) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4621 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4622 (n : Fin 5011) (hn : n.val = 4622) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4622 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4623 (n : Fin 5011) (hn : n.val = 4623) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4623 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4624 (n : Fin 5011) (hn : n.val = 4624) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4624 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4625 (n : Fin 5011) (hn : n.val = 4625) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4625 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4626 (n : Fin 5011) (hn : n.val = 4626) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4626 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4627 (n : Fin 5011) (hn : n.val = 4627) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4627 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4628 (n : Fin 5011) (hn : n.val = 4628) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4628 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4629 (n : Fin 5011) (hn : n.val = 4629) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4629 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4630 (n : Fin 5011) (hn : n.val = 4630) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4630 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4631 (n : Fin 5011) (hn : n.val = 4631) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4631 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4632 (n : Fin 5011) (hn : n.val = 4632) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4632 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4633 (n : Fin 5011) (hn : n.val = 4633) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4633 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4634 (n : Fin 5011) (hn : n.val = 4634) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4634 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4635 (n : Fin 5011) (hn : n.val = 4635) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4635 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4636 (n : Fin 5011) (hn : n.val = 4636) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4636 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4637 (n : Fin 5011) (hn : n.val = 4637) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4637 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4638 (n : Fin 5011) (hn : n.val = 4638) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4638 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4639 (n : Fin 5011) (hn : n.val = 4639) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4639 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4640 (n : Fin 5011) (hn : n.val = 4640) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4640 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4641 (n : Fin 5011) (hn : n.val = 4641) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4641 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4642 (n : Fin 5011) (hn : n.val = 4642) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4642 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4643 (n : Fin 5011) (hn : n.val = 4643) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4643 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4644 (n : Fin 5011) (hn : n.val = 4644) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4644 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4645 (n : Fin 5011) (hn : n.val = 4645) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4645 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4646 (n : Fin 5011) (hn : n.val = 4646) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4646 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4647 (n : Fin 5011) (hn : n.val = 4647) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4647 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4648 (n : Fin 5011) (hn : n.val = 4648) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4648 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4649 (n : Fin 5011) (hn : n.val = 4649) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4649 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4650 (n : Fin 5011) (hn : n.val = 4650) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4650 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4651 (n : Fin 5011) (hn : n.val = 4651) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4651 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4652 (n : Fin 5011) (hn : n.val = 4652) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4652 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4653 (n : Fin 5011) (hn : n.val = 4653) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4653 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4654 (n : Fin 5011) (hn : n.val = 4654) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4654 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4655 (n : Fin 5011) (hn : n.val = 4655) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4655 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4656 (n : Fin 5011) (hn : n.val = 4656) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4656 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4657 (n : Fin 5011) (hn : n.val = 4657) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4657 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4658 (n : Fin 5011) (hn : n.val = 4658) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4658 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4659 (n : Fin 5011) (hn : n.val = 4659) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4659 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4660 (n : Fin 5011) (hn : n.val = 4660) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4660 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4661 (n : Fin 5011) (hn : n.val = 4661) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4661 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4662 (n : Fin 5011) (hn : n.val = 4662) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4662 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4663 (n : Fin 5011) (hn : n.val = 4663) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4663 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4664 (n : Fin 5011) (hn : n.val = 4664) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4664 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4665 (n : Fin 5011) (hn : n.val = 4665) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4665 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4666 (n : Fin 5011) (hn : n.val = 4666) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4666 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4667 (n : Fin 5011) (hn : n.val = 4667) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4667 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4668 (n : Fin 5011) (hn : n.val = 4668) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4668 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4669 (n : Fin 5011) (hn : n.val = 4669) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4669 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4670 (n : Fin 5011) (hn : n.val = 4670) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4670 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4671 (n : Fin 5011) (hn : n.val = 4671) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4671 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4672 (n : Fin 5011) (hn : n.val = 4672) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4672 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4673 (n : Fin 5011) (hn : n.val = 4673) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4673 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4674 (n : Fin 5011) (hn : n.val = 4674) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4674 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4675 (n : Fin 5011) (hn : n.val = 4675) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4675 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4676 (n : Fin 5011) (hn : n.val = 4676) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4676 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4677 (n : Fin 5011) (hn : n.val = 4677) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4677 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4678 (n : Fin 5011) (hn : n.val = 4678) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4678 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4679 (n : Fin 5011) (hn : n.val = 4679) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4679 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4680 (n : Fin 5011) (hn : n.val = 4680) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4680 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4681 (n : Fin 5011) (hn : n.val = 4681) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4681 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4682 (n : Fin 5011) (hn : n.val = 4682) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4682 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4683 (n : Fin 5011) (hn : n.val = 4683) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4683 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4684 (n : Fin 5011) (hn : n.val = 4684) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4684 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4685 (n : Fin 5011) (hn : n.val = 4685) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4685 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4686 (n : Fin 5011) (hn : n.val = 4686) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4686 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4687 (n : Fin 5011) (hn : n.val = 4687) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4687 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4688 (n : Fin 5011) (hn : n.val = 4688) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4688 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4689 (n : Fin 5011) (hn : n.val = 4689) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4689 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4690 (n : Fin 5011) (hn : n.val = 4690) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4690 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4691 (n : Fin 5011) (hn : n.val = 4691) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4691 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4692 (n : Fin 5011) (hn : n.val = 4692) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4692 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4693 (n : Fin 5011) (hn : n.val = 4693) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4693 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4694 (n : Fin 5011) (hn : n.val = 4694) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4694 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4695 (n : Fin 5011) (hn : n.val = 4695) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4695 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4696 (n : Fin 5011) (hn : n.val = 4696) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4696 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4697 (n : Fin 5011) (hn : n.val = 4697) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4697 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4698 (n : Fin 5011) (hn : n.val = 4698) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4698 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_4699 (n : Fin 5011) (hn : n.val = 4699) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 4699 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_5000 (n : Fin 5011) (hn : n.val = 5000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 5000 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_5001 (n : Fin 5011) (hn : n.val = 5001) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 5001 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_5002 (n : Fin 5011) (hn : n.val = 5002) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 5002 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_5003 (n : Fin 5011) (hn : n.val = 5003) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 5003 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_5004 (n : Fin 5011) (hn : n.val = 5004) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 5004 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_5005 (n : Fin 5011) (hn : n.val = 5005) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 5005 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_5006 (n : Fin 5011) (hn : n.val = 5006) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 5006 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_5007 (n : Fin 5011) (hn : n.val = 5007) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 5007 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_5008 (n : Fin 5011) (hn : n.val = 5008) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 5008 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_5009 (n : Fin 5011) (hn : n.val = 5009) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 5009 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_id_5010 (n : Fin 5011) (hn : n.val = 5010) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  change k = 5010 at hn
  subst hn
  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
  decide +kernel +revert

theorem mem_iff_block02 (n : Fin 5011) (hlo : 200 ≤ n.val) (hhi : n.val < 300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_0200 _ rfl
  · exact mem_iff_id_0201 _ rfl
  · exact mem_iff_id_0202 _ rfl
  · exact mem_iff_id_0203 _ rfl
  · exact mem_iff_id_0204 _ rfl
  · exact mem_iff_id_0205 _ rfl
  · exact mem_iff_id_0206 _ rfl
  · exact mem_iff_id_0207 _ rfl
  · exact mem_iff_id_0208 _ rfl
  · exact mem_iff_id_0209 _ rfl
  · exact mem_iff_id_0210 _ rfl
  · exact mem_iff_id_0211 _ rfl
  · exact mem_iff_id_0212 _ rfl
  · exact mem_iff_id_0213 _ rfl
  · exact mem_iff_id_0214 _ rfl
  · exact mem_iff_id_0215 _ rfl
  · exact mem_iff_id_0216 _ rfl
  · exact mem_iff_id_0217 _ rfl
  · exact mem_iff_id_0218 _ rfl
  · exact mem_iff_id_0219 _ rfl
  · exact mem_iff_id_0220 _ rfl
  · exact mem_iff_id_0221 _ rfl
  · exact mem_iff_id_0222 _ rfl
  · exact mem_iff_id_0223 _ rfl
  · exact mem_iff_id_0224 _ rfl
  · exact mem_iff_id_0225 _ rfl
  · exact mem_iff_id_0226 _ rfl
  · exact mem_iff_id_0227 _ rfl
  · exact mem_iff_id_0228 _ rfl
  · exact mem_iff_id_0229 _ rfl
  · exact mem_iff_id_0230 _ rfl
  · exact mem_iff_id_0231 _ rfl
  · exact mem_iff_id_0232 _ rfl
  · exact mem_iff_id_0233 _ rfl
  · exact mem_iff_id_0234 _ rfl
  · exact mem_iff_id_0235 _ rfl
  · exact mem_iff_id_0236 _ rfl
  · exact mem_iff_id_0237 _ rfl
  · exact mem_iff_id_0238 _ rfl
  · exact mem_iff_id_0239 _ rfl
  · exact mem_iff_id_0240 _ rfl
  · exact mem_iff_id_0241 _ rfl
  · exact mem_iff_id_0242 _ rfl
  · exact mem_iff_id_0243 _ rfl
  · exact mem_iff_id_0244 _ rfl
  · exact mem_iff_id_0245 _ rfl
  · exact mem_iff_id_0246 _ rfl
  · exact mem_iff_id_0247 _ rfl
  · exact mem_iff_id_0248 _ rfl
  · exact mem_iff_id_0249 _ rfl
  · exact mem_iff_id_0250 _ rfl
  · exact mem_iff_id_0251 _ rfl
  · exact mem_iff_id_0252 _ rfl
  · exact mem_iff_id_0253 _ rfl
  · exact mem_iff_id_0254 _ rfl
  · exact mem_iff_id_0255 _ rfl
  · exact mem_iff_id_0256 _ rfl
  · exact mem_iff_id_0257 _ rfl
  · exact mem_iff_id_0258 _ rfl
  · exact mem_iff_id_0259 _ rfl
  · exact mem_iff_id_0260 _ rfl
  · exact mem_iff_id_0261 _ rfl
  · exact mem_iff_id_0262 _ rfl
  · exact mem_iff_id_0263 _ rfl
  · exact mem_iff_id_0264 _ rfl
  · exact mem_iff_id_0265 _ rfl
  · exact mem_iff_id_0266 _ rfl
  · exact mem_iff_id_0267 _ rfl
  · exact mem_iff_id_0268 _ rfl
  · exact mem_iff_id_0269 _ rfl
  · exact mem_iff_id_0270 _ rfl
  · exact mem_iff_id_0271 _ rfl
  · exact mem_iff_id_0272 _ rfl
  · exact mem_iff_id_0273 _ rfl
  · exact mem_iff_id_0274 _ rfl
  · exact mem_iff_id_0275 _ rfl
  · exact mem_iff_id_0276 _ rfl
  · exact mem_iff_id_0277 _ rfl
  · exact mem_iff_id_0278 _ rfl
  · exact mem_iff_id_0279 _ rfl
  · exact mem_iff_id_0280 _ rfl
  · exact mem_iff_id_0281 _ rfl
  · exact mem_iff_id_0282 _ rfl
  · exact mem_iff_id_0283 _ rfl
  · exact mem_iff_id_0284 _ rfl
  · exact mem_iff_id_0285 _ rfl
  · exact mem_iff_id_0286 _ rfl
  · exact mem_iff_id_0287 _ rfl
  · exact mem_iff_id_0288 _ rfl
  · exact mem_iff_id_0289 _ rfl
  · exact mem_iff_id_0290 _ rfl
  · exact mem_iff_id_0291 _ rfl
  · exact mem_iff_id_0292 _ rfl
  · exact mem_iff_id_0293 _ rfl
  · exact mem_iff_id_0294 _ rfl
  · exact mem_iff_id_0295 _ rfl
  · exact mem_iff_id_0296 _ rfl
  · exact mem_iff_id_0297 _ rfl
  · exact mem_iff_id_0298 _ rfl
  · exact mem_iff_id_0299 _ rfl

theorem mem_iff_block06 (n : Fin 5011) (hlo : 600 ≤ n.val) (hhi : n.val < 700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_0600 _ rfl
  · exact mem_iff_id_0601 _ rfl
  · exact mem_iff_id_0602 _ rfl
  · exact mem_iff_id_0603 _ rfl
  · exact mem_iff_id_0604 _ rfl
  · exact mem_iff_id_0605 _ rfl
  · exact mem_iff_id_0606 _ rfl
  · exact mem_iff_id_0607 _ rfl
  · exact mem_iff_id_0608 _ rfl
  · exact mem_iff_id_0609 _ rfl
  · exact mem_iff_id_0610 _ rfl
  · exact mem_iff_id_0611 _ rfl
  · exact mem_iff_id_0612 _ rfl
  · exact mem_iff_id_0613 _ rfl
  · exact mem_iff_id_0614 _ rfl
  · exact mem_iff_id_0615 _ rfl
  · exact mem_iff_id_0616 _ rfl
  · exact mem_iff_id_0617 _ rfl
  · exact mem_iff_id_0618 _ rfl
  · exact mem_iff_id_0619 _ rfl
  · exact mem_iff_id_0620 _ rfl
  · exact mem_iff_id_0621 _ rfl
  · exact mem_iff_id_0622 _ rfl
  · exact mem_iff_id_0623 _ rfl
  · exact mem_iff_id_0624 _ rfl
  · exact mem_iff_id_0625 _ rfl
  · exact mem_iff_id_0626 _ rfl
  · exact mem_iff_id_0627 _ rfl
  · exact mem_iff_id_0628 _ rfl
  · exact mem_iff_id_0629 _ rfl
  · exact mem_iff_id_0630 _ rfl
  · exact mem_iff_id_0631 _ rfl
  · exact mem_iff_id_0632 _ rfl
  · exact mem_iff_id_0633 _ rfl
  · exact mem_iff_id_0634 _ rfl
  · exact mem_iff_id_0635 _ rfl
  · exact mem_iff_id_0636 _ rfl
  · exact mem_iff_id_0637 _ rfl
  · exact mem_iff_id_0638 _ rfl
  · exact mem_iff_id_0639 _ rfl
  · exact mem_iff_id_0640 _ rfl
  · exact mem_iff_id_0641 _ rfl
  · exact mem_iff_id_0642 _ rfl
  · exact mem_iff_id_0643 _ rfl
  · exact mem_iff_id_0644 _ rfl
  · exact mem_iff_id_0645 _ rfl
  · exact mem_iff_id_0646 _ rfl
  · exact mem_iff_id_0647 _ rfl
  · exact mem_iff_id_0648 _ rfl
  · exact mem_iff_id_0649 _ rfl
  · exact mem_iff_id_0650 _ rfl
  · exact mem_iff_id_0651 _ rfl
  · exact mem_iff_id_0652 _ rfl
  · exact mem_iff_id_0653 _ rfl
  · exact mem_iff_id_0654 _ rfl
  · exact mem_iff_id_0655 _ rfl
  · exact mem_iff_id_0656 _ rfl
  · exact mem_iff_id_0657 _ rfl
  · exact mem_iff_id_0658 _ rfl
  · exact mem_iff_id_0659 _ rfl
  · exact mem_iff_id_0660 _ rfl
  · exact mem_iff_id_0661 _ rfl
  · exact mem_iff_id_0662 _ rfl
  · exact mem_iff_id_0663 _ rfl
  · exact mem_iff_id_0664 _ rfl
  · exact mem_iff_id_0665 _ rfl
  · exact mem_iff_id_0666 _ rfl
  · exact mem_iff_id_0667 _ rfl
  · exact mem_iff_id_0668 _ rfl
  · exact mem_iff_id_0669 _ rfl
  · exact mem_iff_id_0670 _ rfl
  · exact mem_iff_id_0671 _ rfl
  · exact mem_iff_id_0672 _ rfl
  · exact mem_iff_id_0673 _ rfl
  · exact mem_iff_id_0674 _ rfl
  · exact mem_iff_id_0675 _ rfl
  · exact mem_iff_id_0676 _ rfl
  · exact mem_iff_id_0677 _ rfl
  · exact mem_iff_id_0678 _ rfl
  · exact mem_iff_id_0679 _ rfl
  · exact mem_iff_id_0680 _ rfl
  · exact mem_iff_id_0681 _ rfl
  · exact mem_iff_id_0682 _ rfl
  · exact mem_iff_id_0683 _ rfl
  · exact mem_iff_id_0684 _ rfl
  · exact mem_iff_id_0685 _ rfl
  · exact mem_iff_id_0686 _ rfl
  · exact mem_iff_id_0687 _ rfl
  · exact mem_iff_id_0688 _ rfl
  · exact mem_iff_id_0689 _ rfl
  · exact mem_iff_id_0690 _ rfl
  · exact mem_iff_id_0691 _ rfl
  · exact mem_iff_id_0692 _ rfl
  · exact mem_iff_id_0693 _ rfl
  · exact mem_iff_id_0694 _ rfl
  · exact mem_iff_id_0695 _ rfl
  · exact mem_iff_id_0696 _ rfl
  · exact mem_iff_id_0697 _ rfl
  · exact mem_iff_id_0698 _ rfl
  · exact mem_iff_id_0699 _ rfl

theorem mem_iff_block10 (n : Fin 5011) (hlo : 1000 ≤ n.val) (hhi : n.val < 1100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_1000 _ rfl
  · exact mem_iff_id_1001 _ rfl
  · exact mem_iff_id_1002 _ rfl
  · exact mem_iff_id_1003 _ rfl
  · exact mem_iff_id_1004 _ rfl
  · exact mem_iff_id_1005 _ rfl
  · exact mem_iff_id_1006 _ rfl
  · exact mem_iff_id_1007 _ rfl
  · exact mem_iff_id_1008 _ rfl
  · exact mem_iff_id_1009 _ rfl
  · exact mem_iff_id_1010 _ rfl
  · exact mem_iff_id_1011 _ rfl
  · exact mem_iff_id_1012 _ rfl
  · exact mem_iff_id_1013 _ rfl
  · exact mem_iff_id_1014 _ rfl
  · exact mem_iff_id_1015 _ rfl
  · exact mem_iff_id_1016 _ rfl
  · exact mem_iff_id_1017 _ rfl
  · exact mem_iff_id_1018 _ rfl
  · exact mem_iff_id_1019 _ rfl
  · exact mem_iff_id_1020 _ rfl
  · exact mem_iff_id_1021 _ rfl
  · exact mem_iff_id_1022 _ rfl
  · exact mem_iff_id_1023 _ rfl
  · exact mem_iff_id_1024 _ rfl
  · exact mem_iff_id_1025 _ rfl
  · exact mem_iff_id_1026 _ rfl
  · exact mem_iff_id_1027 _ rfl
  · exact mem_iff_id_1028 _ rfl
  · exact mem_iff_id_1029 _ rfl
  · exact mem_iff_id_1030 _ rfl
  · exact mem_iff_id_1031 _ rfl
  · exact mem_iff_id_1032 _ rfl
  · exact mem_iff_id_1033 _ rfl
  · exact mem_iff_id_1034 _ rfl
  · exact mem_iff_id_1035 _ rfl
  · exact mem_iff_id_1036 _ rfl
  · exact mem_iff_id_1037 _ rfl
  · exact mem_iff_id_1038 _ rfl
  · exact mem_iff_id_1039 _ rfl
  · exact mem_iff_id_1040 _ rfl
  · exact mem_iff_id_1041 _ rfl
  · exact mem_iff_id_1042 _ rfl
  · exact mem_iff_id_1043 _ rfl
  · exact mem_iff_id_1044 _ rfl
  · exact mem_iff_id_1045 _ rfl
  · exact mem_iff_id_1046 _ rfl
  · exact mem_iff_id_1047 _ rfl
  · exact mem_iff_id_1048 _ rfl
  · exact mem_iff_id_1049 _ rfl
  · exact mem_iff_id_1050 _ rfl
  · exact mem_iff_id_1051 _ rfl
  · exact mem_iff_id_1052 _ rfl
  · exact mem_iff_id_1053 _ rfl
  · exact mem_iff_id_1054 _ rfl
  · exact mem_iff_id_1055 _ rfl
  · exact mem_iff_id_1056 _ rfl
  · exact mem_iff_id_1057 _ rfl
  · exact mem_iff_id_1058 _ rfl
  · exact mem_iff_id_1059 _ rfl
  · exact mem_iff_id_1060 _ rfl
  · exact mem_iff_id_1061 _ rfl
  · exact mem_iff_id_1062 _ rfl
  · exact mem_iff_id_1063 _ rfl
  · exact mem_iff_id_1064 _ rfl
  · exact mem_iff_id_1065 _ rfl
  · exact mem_iff_id_1066 _ rfl
  · exact mem_iff_id_1067 _ rfl
  · exact mem_iff_id_1068 _ rfl
  · exact mem_iff_id_1069 _ rfl
  · exact mem_iff_id_1070 _ rfl
  · exact mem_iff_id_1071 _ rfl
  · exact mem_iff_id_1072 _ rfl
  · exact mem_iff_id_1073 _ rfl
  · exact mem_iff_id_1074 _ rfl
  · exact mem_iff_id_1075 _ rfl
  · exact mem_iff_id_1076 _ rfl
  · exact mem_iff_id_1077 _ rfl
  · exact mem_iff_id_1078 _ rfl
  · exact mem_iff_id_1079 _ rfl
  · exact mem_iff_id_1080 _ rfl
  · exact mem_iff_id_1081 _ rfl
  · exact mem_iff_id_1082 _ rfl
  · exact mem_iff_id_1083 _ rfl
  · exact mem_iff_id_1084 _ rfl
  · exact mem_iff_id_1085 _ rfl
  · exact mem_iff_id_1086 _ rfl
  · exact mem_iff_id_1087 _ rfl
  · exact mem_iff_id_1088 _ rfl
  · exact mem_iff_id_1089 _ rfl
  · exact mem_iff_id_1090 _ rfl
  · exact mem_iff_id_1091 _ rfl
  · exact mem_iff_id_1092 _ rfl
  · exact mem_iff_id_1093 _ rfl
  · exact mem_iff_id_1094 _ rfl
  · exact mem_iff_id_1095 _ rfl
  · exact mem_iff_id_1096 _ rfl
  · exact mem_iff_id_1097 _ rfl
  · exact mem_iff_id_1098 _ rfl
  · exact mem_iff_id_1099 _ rfl

theorem mem_iff_block14 (n : Fin 5011) (hlo : 1400 ≤ n.val) (hhi : n.val < 1500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_1400 _ rfl
  · exact mem_iff_id_1401 _ rfl
  · exact mem_iff_id_1402 _ rfl
  · exact mem_iff_id_1403 _ rfl
  · exact mem_iff_id_1404 _ rfl
  · exact mem_iff_id_1405 _ rfl
  · exact mem_iff_id_1406 _ rfl
  · exact mem_iff_id_1407 _ rfl
  · exact mem_iff_id_1408 _ rfl
  · exact mem_iff_id_1409 _ rfl
  · exact mem_iff_id_1410 _ rfl
  · exact mem_iff_id_1411 _ rfl
  · exact mem_iff_id_1412 _ rfl
  · exact mem_iff_id_1413 _ rfl
  · exact mem_iff_id_1414 _ rfl
  · exact mem_iff_id_1415 _ rfl
  · exact mem_iff_id_1416 _ rfl
  · exact mem_iff_id_1417 _ rfl
  · exact mem_iff_id_1418 _ rfl
  · exact mem_iff_id_1419 _ rfl
  · exact mem_iff_id_1420 _ rfl
  · exact mem_iff_id_1421 _ rfl
  · exact mem_iff_id_1422 _ rfl
  · exact mem_iff_id_1423 _ rfl
  · exact mem_iff_id_1424 _ rfl
  · exact mem_iff_id_1425 _ rfl
  · exact mem_iff_id_1426 _ rfl
  · exact mem_iff_id_1427 _ rfl
  · exact mem_iff_id_1428 _ rfl
  · exact mem_iff_id_1429 _ rfl
  · exact mem_iff_id_1430 _ rfl
  · exact mem_iff_id_1431 _ rfl
  · exact mem_iff_id_1432 _ rfl
  · exact mem_iff_id_1433 _ rfl
  · exact mem_iff_id_1434 _ rfl
  · exact mem_iff_id_1435 _ rfl
  · exact mem_iff_id_1436 _ rfl
  · exact mem_iff_id_1437 _ rfl
  · exact mem_iff_id_1438 _ rfl
  · exact mem_iff_id_1439 _ rfl
  · exact mem_iff_id_1440 _ rfl
  · exact mem_iff_id_1441 _ rfl
  · exact mem_iff_id_1442 _ rfl
  · exact mem_iff_id_1443 _ rfl
  · exact mem_iff_id_1444 _ rfl
  · exact mem_iff_id_1445 _ rfl
  · exact mem_iff_id_1446 _ rfl
  · exact mem_iff_id_1447 _ rfl
  · exact mem_iff_id_1448 _ rfl
  · exact mem_iff_id_1449 _ rfl
  · exact mem_iff_id_1450 _ rfl
  · exact mem_iff_id_1451 _ rfl
  · exact mem_iff_id_1452 _ rfl
  · exact mem_iff_id_1453 _ rfl
  · exact mem_iff_id_1454 _ rfl
  · exact mem_iff_id_1455 _ rfl
  · exact mem_iff_id_1456 _ rfl
  · exact mem_iff_id_1457 _ rfl
  · exact mem_iff_id_1458 _ rfl
  · exact mem_iff_id_1459 _ rfl
  · exact mem_iff_id_1460 _ rfl
  · exact mem_iff_id_1461 _ rfl
  · exact mem_iff_id_1462 _ rfl
  · exact mem_iff_id_1463 _ rfl
  · exact mem_iff_id_1464 _ rfl
  · exact mem_iff_id_1465 _ rfl
  · exact mem_iff_id_1466 _ rfl
  · exact mem_iff_id_1467 _ rfl
  · exact mem_iff_id_1468 _ rfl
  · exact mem_iff_id_1469 _ rfl
  · exact mem_iff_id_1470 _ rfl
  · exact mem_iff_id_1471 _ rfl
  · exact mem_iff_id_1472 _ rfl
  · exact mem_iff_id_1473 _ rfl
  · exact mem_iff_id_1474 _ rfl
  · exact mem_iff_id_1475 _ rfl
  · exact mem_iff_id_1476 _ rfl
  · exact mem_iff_id_1477 _ rfl
  · exact mem_iff_id_1478 _ rfl
  · exact mem_iff_id_1479 _ rfl
  · exact mem_iff_id_1480 _ rfl
  · exact mem_iff_id_1481 _ rfl
  · exact mem_iff_id_1482 _ rfl
  · exact mem_iff_id_1483 _ rfl
  · exact mem_iff_id_1484 _ rfl
  · exact mem_iff_id_1485 _ rfl
  · exact mem_iff_id_1486 _ rfl
  · exact mem_iff_id_1487 _ rfl
  · exact mem_iff_id_1488 _ rfl
  · exact mem_iff_id_1489 _ rfl
  · exact mem_iff_id_1490 _ rfl
  · exact mem_iff_id_1491 _ rfl
  · exact mem_iff_id_1492 _ rfl
  · exact mem_iff_id_1493 _ rfl
  · exact mem_iff_id_1494 _ rfl
  · exact mem_iff_id_1495 _ rfl
  · exact mem_iff_id_1496 _ rfl
  · exact mem_iff_id_1497 _ rfl
  · exact mem_iff_id_1498 _ rfl
  · exact mem_iff_id_1499 _ rfl

theorem mem_iff_block18 (n : Fin 5011) (hlo : 1800 ≤ n.val) (hhi : n.val < 1900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_1800 _ rfl
  · exact mem_iff_id_1801 _ rfl
  · exact mem_iff_id_1802 _ rfl
  · exact mem_iff_id_1803 _ rfl
  · exact mem_iff_id_1804 _ rfl
  · exact mem_iff_id_1805 _ rfl
  · exact mem_iff_id_1806 _ rfl
  · exact mem_iff_id_1807 _ rfl
  · exact mem_iff_id_1808 _ rfl
  · exact mem_iff_id_1809 _ rfl
  · exact mem_iff_id_1810 _ rfl
  · exact mem_iff_id_1811 _ rfl
  · exact mem_iff_id_1812 _ rfl
  · exact mem_iff_id_1813 _ rfl
  · exact mem_iff_id_1814 _ rfl
  · exact mem_iff_id_1815 _ rfl
  · exact mem_iff_id_1816 _ rfl
  · exact mem_iff_id_1817 _ rfl
  · exact mem_iff_id_1818 _ rfl
  · exact mem_iff_id_1819 _ rfl
  · exact mem_iff_id_1820 _ rfl
  · exact mem_iff_id_1821 _ rfl
  · exact mem_iff_id_1822 _ rfl
  · exact mem_iff_id_1823 _ rfl
  · exact mem_iff_id_1824 _ rfl
  · exact mem_iff_id_1825 _ rfl
  · exact mem_iff_id_1826 _ rfl
  · exact mem_iff_id_1827 _ rfl
  · exact mem_iff_id_1828 _ rfl
  · exact mem_iff_id_1829 _ rfl
  · exact mem_iff_id_1830 _ rfl
  · exact mem_iff_id_1831 _ rfl
  · exact mem_iff_id_1832 _ rfl
  · exact mem_iff_id_1833 _ rfl
  · exact mem_iff_id_1834 _ rfl
  · exact mem_iff_id_1835 _ rfl
  · exact mem_iff_id_1836 _ rfl
  · exact mem_iff_id_1837 _ rfl
  · exact mem_iff_id_1838 _ rfl
  · exact mem_iff_id_1839 _ rfl
  · exact mem_iff_id_1840 _ rfl
  · exact mem_iff_id_1841 _ rfl
  · exact mem_iff_id_1842 _ rfl
  · exact mem_iff_id_1843 _ rfl
  · exact mem_iff_id_1844 _ rfl
  · exact mem_iff_id_1845 _ rfl
  · exact mem_iff_id_1846 _ rfl
  · exact mem_iff_id_1847 _ rfl
  · exact mem_iff_id_1848 _ rfl
  · exact mem_iff_id_1849 _ rfl
  · exact mem_iff_id_1850 _ rfl
  · exact mem_iff_id_1851 _ rfl
  · exact mem_iff_id_1852 _ rfl
  · exact mem_iff_id_1853 _ rfl
  · exact mem_iff_id_1854 _ rfl
  · exact mem_iff_id_1855 _ rfl
  · exact mem_iff_id_1856 _ rfl
  · exact mem_iff_id_1857 _ rfl
  · exact mem_iff_id_1858 _ rfl
  · exact mem_iff_id_1859 _ rfl
  · exact mem_iff_id_1860 _ rfl
  · exact mem_iff_id_1861 _ rfl
  · exact mem_iff_id_1862 _ rfl
  · exact mem_iff_id_1863 _ rfl
  · exact mem_iff_id_1864 _ rfl
  · exact mem_iff_id_1865 _ rfl
  · exact mem_iff_id_1866 _ rfl
  · exact mem_iff_id_1867 _ rfl
  · exact mem_iff_id_1868 _ rfl
  · exact mem_iff_id_1869 _ rfl
  · exact mem_iff_id_1870 _ rfl
  · exact mem_iff_id_1871 _ rfl
  · exact mem_iff_id_1872 _ rfl
  · exact mem_iff_id_1873 _ rfl
  · exact mem_iff_id_1874 _ rfl
  · exact mem_iff_id_1875 _ rfl
  · exact mem_iff_id_1876 _ rfl
  · exact mem_iff_id_1877 _ rfl
  · exact mem_iff_id_1878 _ rfl
  · exact mem_iff_id_1879 _ rfl
  · exact mem_iff_id_1880 _ rfl
  · exact mem_iff_id_1881 _ rfl
  · exact mem_iff_id_1882 _ rfl
  · exact mem_iff_id_1883 _ rfl
  · exact mem_iff_id_1884 _ rfl
  · exact mem_iff_id_1885 _ rfl
  · exact mem_iff_id_1886 _ rfl
  · exact mem_iff_id_1887 _ rfl
  · exact mem_iff_id_1888 _ rfl
  · exact mem_iff_id_1889 _ rfl
  · exact mem_iff_id_1890 _ rfl
  · exact mem_iff_id_1891 _ rfl
  · exact mem_iff_id_1892 _ rfl
  · exact mem_iff_id_1893 _ rfl
  · exact mem_iff_id_1894 _ rfl
  · exact mem_iff_id_1895 _ rfl
  · exact mem_iff_id_1896 _ rfl
  · exact mem_iff_id_1897 _ rfl
  · exact mem_iff_id_1898 _ rfl
  · exact mem_iff_id_1899 _ rfl

theorem mem_iff_block22 (n : Fin 5011) (hlo : 2200 ≤ n.val) (hhi : n.val < 2300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_2200 _ rfl
  · exact mem_iff_id_2201 _ rfl
  · exact mem_iff_id_2202 _ rfl
  · exact mem_iff_id_2203 _ rfl
  · exact mem_iff_id_2204 _ rfl
  · exact mem_iff_id_2205 _ rfl
  · exact mem_iff_id_2206 _ rfl
  · exact mem_iff_id_2207 _ rfl
  · exact mem_iff_id_2208 _ rfl
  · exact mem_iff_id_2209 _ rfl
  · exact mem_iff_id_2210 _ rfl
  · exact mem_iff_id_2211 _ rfl
  · exact mem_iff_id_2212 _ rfl
  · exact mem_iff_id_2213 _ rfl
  · exact mem_iff_id_2214 _ rfl
  · exact mem_iff_id_2215 _ rfl
  · exact mem_iff_id_2216 _ rfl
  · exact mem_iff_id_2217 _ rfl
  · exact mem_iff_id_2218 _ rfl
  · exact mem_iff_id_2219 _ rfl
  · exact mem_iff_id_2220 _ rfl
  · exact mem_iff_id_2221 _ rfl
  · exact mem_iff_id_2222 _ rfl
  · exact mem_iff_id_2223 _ rfl
  · exact mem_iff_id_2224 _ rfl
  · exact mem_iff_id_2225 _ rfl
  · exact mem_iff_id_2226 _ rfl
  · exact mem_iff_id_2227 _ rfl
  · exact mem_iff_id_2228 _ rfl
  · exact mem_iff_id_2229 _ rfl
  · exact mem_iff_id_2230 _ rfl
  · exact mem_iff_id_2231 _ rfl
  · exact mem_iff_id_2232 _ rfl
  · exact mem_iff_id_2233 _ rfl
  · exact mem_iff_id_2234 _ rfl
  · exact mem_iff_id_2235 _ rfl
  · exact mem_iff_id_2236 _ rfl
  · exact mem_iff_id_2237 _ rfl
  · exact mem_iff_id_2238 _ rfl
  · exact mem_iff_id_2239 _ rfl
  · exact mem_iff_id_2240 _ rfl
  · exact mem_iff_id_2241 _ rfl
  · exact mem_iff_id_2242 _ rfl
  · exact mem_iff_id_2243 _ rfl
  · exact mem_iff_id_2244 _ rfl
  · exact mem_iff_id_2245 _ rfl
  · exact mem_iff_id_2246 _ rfl
  · exact mem_iff_id_2247 _ rfl
  · exact mem_iff_id_2248 _ rfl
  · exact mem_iff_id_2249 _ rfl
  · exact mem_iff_id_2250 _ rfl
  · exact mem_iff_id_2251 _ rfl
  · exact mem_iff_id_2252 _ rfl
  · exact mem_iff_id_2253 _ rfl
  · exact mem_iff_id_2254 _ rfl
  · exact mem_iff_id_2255 _ rfl
  · exact mem_iff_id_2256 _ rfl
  · exact mem_iff_id_2257 _ rfl
  · exact mem_iff_id_2258 _ rfl
  · exact mem_iff_id_2259 _ rfl
  · exact mem_iff_id_2260 _ rfl
  · exact mem_iff_id_2261 _ rfl
  · exact mem_iff_id_2262 _ rfl
  · exact mem_iff_id_2263 _ rfl
  · exact mem_iff_id_2264 _ rfl
  · exact mem_iff_id_2265 _ rfl
  · exact mem_iff_id_2266 _ rfl
  · exact mem_iff_id_2267 _ rfl
  · exact mem_iff_id_2268 _ rfl
  · exact mem_iff_id_2269 _ rfl
  · exact mem_iff_id_2270 _ rfl
  · exact mem_iff_id_2271 _ rfl
  · exact mem_iff_id_2272 _ rfl
  · exact mem_iff_id_2273 _ rfl
  · exact mem_iff_id_2274 _ rfl
  · exact mem_iff_id_2275 _ rfl
  · exact mem_iff_id_2276 _ rfl
  · exact mem_iff_id_2277 _ rfl
  · exact mem_iff_id_2278 _ rfl
  · exact mem_iff_id_2279 _ rfl
  · exact mem_iff_id_2280 _ rfl
  · exact mem_iff_id_2281 _ rfl
  · exact mem_iff_id_2282 _ rfl
  · exact mem_iff_id_2283 _ rfl
  · exact mem_iff_id_2284 _ rfl
  · exact mem_iff_id_2285 _ rfl
  · exact mem_iff_id_2286 _ rfl
  · exact mem_iff_id_2287 _ rfl
  · exact mem_iff_id_2288 _ rfl
  · exact mem_iff_id_2289 _ rfl
  · exact mem_iff_id_2290 _ rfl
  · exact mem_iff_id_2291 _ rfl
  · exact mem_iff_id_2292 _ rfl
  · exact mem_iff_id_2293 _ rfl
  · exact mem_iff_id_2294 _ rfl
  · exact mem_iff_id_2295 _ rfl
  · exact mem_iff_id_2296 _ rfl
  · exact mem_iff_id_2297 _ rfl
  · exact mem_iff_id_2298 _ rfl
  · exact mem_iff_id_2299 _ rfl

theorem mem_iff_block26 (n : Fin 5011) (hlo : 2600 ≤ n.val) (hhi : n.val < 2700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_2600 _ rfl
  · exact mem_iff_id_2601 _ rfl
  · exact mem_iff_id_2602 _ rfl
  · exact mem_iff_id_2603 _ rfl
  · exact mem_iff_id_2604 _ rfl
  · exact mem_iff_id_2605 _ rfl
  · exact mem_iff_id_2606 _ rfl
  · exact mem_iff_id_2607 _ rfl
  · exact mem_iff_id_2608 _ rfl
  · exact mem_iff_id_2609 _ rfl
  · exact mem_iff_id_2610 _ rfl
  · exact mem_iff_id_2611 _ rfl
  · exact mem_iff_id_2612 _ rfl
  · exact mem_iff_id_2613 _ rfl
  · exact mem_iff_id_2614 _ rfl
  · exact mem_iff_id_2615 _ rfl
  · exact mem_iff_id_2616 _ rfl
  · exact mem_iff_id_2617 _ rfl
  · exact mem_iff_id_2618 _ rfl
  · exact mem_iff_id_2619 _ rfl
  · exact mem_iff_id_2620 _ rfl
  · exact mem_iff_id_2621 _ rfl
  · exact mem_iff_id_2622 _ rfl
  · exact mem_iff_id_2623 _ rfl
  · exact mem_iff_id_2624 _ rfl
  · exact mem_iff_id_2625 _ rfl
  · exact mem_iff_id_2626 _ rfl
  · exact mem_iff_id_2627 _ rfl
  · exact mem_iff_id_2628 _ rfl
  · exact mem_iff_id_2629 _ rfl
  · exact mem_iff_id_2630 _ rfl
  · exact mem_iff_id_2631 _ rfl
  · exact mem_iff_id_2632 _ rfl
  · exact mem_iff_id_2633 _ rfl
  · exact mem_iff_id_2634 _ rfl
  · exact mem_iff_id_2635 _ rfl
  · exact mem_iff_id_2636 _ rfl
  · exact mem_iff_id_2637 _ rfl
  · exact mem_iff_id_2638 _ rfl
  · exact mem_iff_id_2639 _ rfl
  · exact mem_iff_id_2640 _ rfl
  · exact mem_iff_id_2641 _ rfl
  · exact mem_iff_id_2642 _ rfl
  · exact mem_iff_id_2643 _ rfl
  · exact mem_iff_id_2644 _ rfl
  · exact mem_iff_id_2645 _ rfl
  · exact mem_iff_id_2646 _ rfl
  · exact mem_iff_id_2647 _ rfl
  · exact mem_iff_id_2648 _ rfl
  · exact mem_iff_id_2649 _ rfl
  · exact mem_iff_id_2650 _ rfl
  · exact mem_iff_id_2651 _ rfl
  · exact mem_iff_id_2652 _ rfl
  · exact mem_iff_id_2653 _ rfl
  · exact mem_iff_id_2654 _ rfl
  · exact mem_iff_id_2655 _ rfl
  · exact mem_iff_id_2656 _ rfl
  · exact mem_iff_id_2657 _ rfl
  · exact mem_iff_id_2658 _ rfl
  · exact mem_iff_id_2659 _ rfl
  · exact mem_iff_id_2660 _ rfl
  · exact mem_iff_id_2661 _ rfl
  · exact mem_iff_id_2662 _ rfl
  · exact mem_iff_id_2663 _ rfl
  · exact mem_iff_id_2664 _ rfl
  · exact mem_iff_id_2665 _ rfl
  · exact mem_iff_id_2666 _ rfl
  · exact mem_iff_id_2667 _ rfl
  · exact mem_iff_id_2668 _ rfl
  · exact mem_iff_id_2669 _ rfl
  · exact mem_iff_id_2670 _ rfl
  · exact mem_iff_id_2671 _ rfl
  · exact mem_iff_id_2672 _ rfl
  · exact mem_iff_id_2673 _ rfl
  · exact mem_iff_id_2674 _ rfl
  · exact mem_iff_id_2675 _ rfl
  · exact mem_iff_id_2676 _ rfl
  · exact mem_iff_id_2677 _ rfl
  · exact mem_iff_id_2678 _ rfl
  · exact mem_iff_id_2679 _ rfl
  · exact mem_iff_id_2680 _ rfl
  · exact mem_iff_id_2681 _ rfl
  · exact mem_iff_id_2682 _ rfl
  · exact mem_iff_id_2683 _ rfl
  · exact mem_iff_id_2684 _ rfl
  · exact mem_iff_id_2685 _ rfl
  · exact mem_iff_id_2686 _ rfl
  · exact mem_iff_id_2687 _ rfl
  · exact mem_iff_id_2688 _ rfl
  · exact mem_iff_id_2689 _ rfl
  · exact mem_iff_id_2690 _ rfl
  · exact mem_iff_id_2691 _ rfl
  · exact mem_iff_id_2692 _ rfl
  · exact mem_iff_id_2693 _ rfl
  · exact mem_iff_id_2694 _ rfl
  · exact mem_iff_id_2695 _ rfl
  · exact mem_iff_id_2696 _ rfl
  · exact mem_iff_id_2697 _ rfl
  · exact mem_iff_id_2698 _ rfl
  · exact mem_iff_id_2699 _ rfl

theorem mem_iff_block30 (n : Fin 5011) (hlo : 3000 ≤ n.val) (hhi : n.val < 3100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_3000 _ rfl
  · exact mem_iff_id_3001 _ rfl
  · exact mem_iff_id_3002 _ rfl
  · exact mem_iff_id_3003 _ rfl
  · exact mem_iff_id_3004 _ rfl
  · exact mem_iff_id_3005 _ rfl
  · exact mem_iff_id_3006 _ rfl
  · exact mem_iff_id_3007 _ rfl
  · exact mem_iff_id_3008 _ rfl
  · exact mem_iff_id_3009 _ rfl
  · exact mem_iff_id_3010 _ rfl
  · exact mem_iff_id_3011 _ rfl
  · exact mem_iff_id_3012 _ rfl
  · exact mem_iff_id_3013 _ rfl
  · exact mem_iff_id_3014 _ rfl
  · exact mem_iff_id_3015 _ rfl
  · exact mem_iff_id_3016 _ rfl
  · exact mem_iff_id_3017 _ rfl
  · exact mem_iff_id_3018 _ rfl
  · exact mem_iff_id_3019 _ rfl
  · exact mem_iff_id_3020 _ rfl
  · exact mem_iff_id_3021 _ rfl
  · exact mem_iff_id_3022 _ rfl
  · exact mem_iff_id_3023 _ rfl
  · exact mem_iff_id_3024 _ rfl
  · exact mem_iff_id_3025 _ rfl
  · exact mem_iff_id_3026 _ rfl
  · exact mem_iff_id_3027 _ rfl
  · exact mem_iff_id_3028 _ rfl
  · exact mem_iff_id_3029 _ rfl
  · exact mem_iff_id_3030 _ rfl
  · exact mem_iff_id_3031 _ rfl
  · exact mem_iff_id_3032 _ rfl
  · exact mem_iff_id_3033 _ rfl
  · exact mem_iff_id_3034 _ rfl
  · exact mem_iff_id_3035 _ rfl
  · exact mem_iff_id_3036 _ rfl
  · exact mem_iff_id_3037 _ rfl
  · exact mem_iff_id_3038 _ rfl
  · exact mem_iff_id_3039 _ rfl
  · exact mem_iff_id_3040 _ rfl
  · exact mem_iff_id_3041 _ rfl
  · exact mem_iff_id_3042 _ rfl
  · exact mem_iff_id_3043 _ rfl
  · exact mem_iff_id_3044 _ rfl
  · exact mem_iff_id_3045 _ rfl
  · exact mem_iff_id_3046 _ rfl
  · exact mem_iff_id_3047 _ rfl
  · exact mem_iff_id_3048 _ rfl
  · exact mem_iff_id_3049 _ rfl
  · exact mem_iff_id_3050 _ rfl
  · exact mem_iff_id_3051 _ rfl
  · exact mem_iff_id_3052 _ rfl
  · exact mem_iff_id_3053 _ rfl
  · exact mem_iff_id_3054 _ rfl
  · exact mem_iff_id_3055 _ rfl
  · exact mem_iff_id_3056 _ rfl
  · exact mem_iff_id_3057 _ rfl
  · exact mem_iff_id_3058 _ rfl
  · exact mem_iff_id_3059 _ rfl
  · exact mem_iff_id_3060 _ rfl
  · exact mem_iff_id_3061 _ rfl
  · exact mem_iff_id_3062 _ rfl
  · exact mem_iff_id_3063 _ rfl
  · exact mem_iff_id_3064 _ rfl
  · exact mem_iff_id_3065 _ rfl
  · exact mem_iff_id_3066 _ rfl
  · exact mem_iff_id_3067 _ rfl
  · exact mem_iff_id_3068 _ rfl
  · exact mem_iff_id_3069 _ rfl
  · exact mem_iff_id_3070 _ rfl
  · exact mem_iff_id_3071 _ rfl
  · exact mem_iff_id_3072 _ rfl
  · exact mem_iff_id_3073 _ rfl
  · exact mem_iff_id_3074 _ rfl
  · exact mem_iff_id_3075 _ rfl
  · exact mem_iff_id_3076 _ rfl
  · exact mem_iff_id_3077 _ rfl
  · exact mem_iff_id_3078 _ rfl
  · exact mem_iff_id_3079 _ rfl
  · exact mem_iff_id_3080 _ rfl
  · exact mem_iff_id_3081 _ rfl
  · exact mem_iff_id_3082 _ rfl
  · exact mem_iff_id_3083 _ rfl
  · exact mem_iff_id_3084 _ rfl
  · exact mem_iff_id_3085 _ rfl
  · exact mem_iff_id_3086 _ rfl
  · exact mem_iff_id_3087 _ rfl
  · exact mem_iff_id_3088 _ rfl
  · exact mem_iff_id_3089 _ rfl
  · exact mem_iff_id_3090 _ rfl
  · exact mem_iff_id_3091 _ rfl
  · exact mem_iff_id_3092 _ rfl
  · exact mem_iff_id_3093 _ rfl
  · exact mem_iff_id_3094 _ rfl
  · exact mem_iff_id_3095 _ rfl
  · exact mem_iff_id_3096 _ rfl
  · exact mem_iff_id_3097 _ rfl
  · exact mem_iff_id_3098 _ rfl
  · exact mem_iff_id_3099 _ rfl

theorem mem_iff_block34 (n : Fin 5011) (hlo : 3400 ≤ n.val) (hhi : n.val < 3500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_3400 _ rfl
  · exact mem_iff_id_3401 _ rfl
  · exact mem_iff_id_3402 _ rfl
  · exact mem_iff_id_3403 _ rfl
  · exact mem_iff_id_3404 _ rfl
  · exact mem_iff_id_3405 _ rfl
  · exact mem_iff_id_3406 _ rfl
  · exact mem_iff_id_3407 _ rfl
  · exact mem_iff_id_3408 _ rfl
  · exact mem_iff_id_3409 _ rfl
  · exact mem_iff_id_3410 _ rfl
  · exact mem_iff_id_3411 _ rfl
  · exact mem_iff_id_3412 _ rfl
  · exact mem_iff_id_3413 _ rfl
  · exact mem_iff_id_3414 _ rfl
  · exact mem_iff_id_3415 _ rfl
  · exact mem_iff_id_3416 _ rfl
  · exact mem_iff_id_3417 _ rfl
  · exact mem_iff_id_3418 _ rfl
  · exact mem_iff_id_3419 _ rfl
  · exact mem_iff_id_3420 _ rfl
  · exact mem_iff_id_3421 _ rfl
  · exact mem_iff_id_3422 _ rfl
  · exact mem_iff_id_3423 _ rfl
  · exact mem_iff_id_3424 _ rfl
  · exact mem_iff_id_3425 _ rfl
  · exact mem_iff_id_3426 _ rfl
  · exact mem_iff_id_3427 _ rfl
  · exact mem_iff_id_3428 _ rfl
  · exact mem_iff_id_3429 _ rfl
  · exact mem_iff_id_3430 _ rfl
  · exact mem_iff_id_3431 _ rfl
  · exact mem_iff_id_3432 _ rfl
  · exact mem_iff_id_3433 _ rfl
  · exact mem_iff_id_3434 _ rfl
  · exact mem_iff_id_3435 _ rfl
  · exact mem_iff_id_3436 _ rfl
  · exact mem_iff_id_3437 _ rfl
  · exact mem_iff_id_3438 _ rfl
  · exact mem_iff_id_3439 _ rfl
  · exact mem_iff_id_3440 _ rfl
  · exact mem_iff_id_3441 _ rfl
  · exact mem_iff_id_3442 _ rfl
  · exact mem_iff_id_3443 _ rfl
  · exact mem_iff_id_3444 _ rfl
  · exact mem_iff_id_3445 _ rfl
  · exact mem_iff_id_3446 _ rfl
  · exact mem_iff_id_3447 _ rfl
  · exact mem_iff_id_3448 _ rfl
  · exact mem_iff_id_3449 _ rfl
  · exact mem_iff_id_3450 _ rfl
  · exact mem_iff_id_3451 _ rfl
  · exact mem_iff_id_3452 _ rfl
  · exact mem_iff_id_3453 _ rfl
  · exact mem_iff_id_3454 _ rfl
  · exact mem_iff_id_3455 _ rfl
  · exact mem_iff_id_3456 _ rfl
  · exact mem_iff_id_3457 _ rfl
  · exact mem_iff_id_3458 _ rfl
  · exact mem_iff_id_3459 _ rfl
  · exact mem_iff_id_3460 _ rfl
  · exact mem_iff_id_3461 _ rfl
  · exact mem_iff_id_3462 _ rfl
  · exact mem_iff_id_3463 _ rfl
  · exact mem_iff_id_3464 _ rfl
  · exact mem_iff_id_3465 _ rfl
  · exact mem_iff_id_3466 _ rfl
  · exact mem_iff_id_3467 _ rfl
  · exact mem_iff_id_3468 _ rfl
  · exact mem_iff_id_3469 _ rfl
  · exact mem_iff_id_3470 _ rfl
  · exact mem_iff_id_3471 _ rfl
  · exact mem_iff_id_3472 _ rfl
  · exact mem_iff_id_3473 _ rfl
  · exact mem_iff_id_3474 _ rfl
  · exact mem_iff_id_3475 _ rfl
  · exact mem_iff_id_3476 _ rfl
  · exact mem_iff_id_3477 _ rfl
  · exact mem_iff_id_3478 _ rfl
  · exact mem_iff_id_3479 _ rfl
  · exact mem_iff_id_3480 _ rfl
  · exact mem_iff_id_3481 _ rfl
  · exact mem_iff_id_3482 _ rfl
  · exact mem_iff_id_3483 _ rfl
  · exact mem_iff_id_3484 _ rfl
  · exact mem_iff_id_3485 _ rfl
  · exact mem_iff_id_3486 _ rfl
  · exact mem_iff_id_3487 _ rfl
  · exact mem_iff_id_3488 _ rfl
  · exact mem_iff_id_3489 _ rfl
  · exact mem_iff_id_3490 _ rfl
  · exact mem_iff_id_3491 _ rfl
  · exact mem_iff_id_3492 _ rfl
  · exact mem_iff_id_3493 _ rfl
  · exact mem_iff_id_3494 _ rfl
  · exact mem_iff_id_3495 _ rfl
  · exact mem_iff_id_3496 _ rfl
  · exact mem_iff_id_3497 _ rfl
  · exact mem_iff_id_3498 _ rfl
  · exact mem_iff_id_3499 _ rfl

theorem mem_iff_block38 (n : Fin 5011) (hlo : 3800 ≤ n.val) (hhi : n.val < 3900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_3800 _ rfl
  · exact mem_iff_id_3801 _ rfl
  · exact mem_iff_id_3802 _ rfl
  · exact mem_iff_id_3803 _ rfl
  · exact mem_iff_id_3804 _ rfl
  · exact mem_iff_id_3805 _ rfl
  · exact mem_iff_id_3806 _ rfl
  · exact mem_iff_id_3807 _ rfl
  · exact mem_iff_id_3808 _ rfl
  · exact mem_iff_id_3809 _ rfl
  · exact mem_iff_id_3810 _ rfl
  · exact mem_iff_id_3811 _ rfl
  · exact mem_iff_id_3812 _ rfl
  · exact mem_iff_id_3813 _ rfl
  · exact mem_iff_id_3814 _ rfl
  · exact mem_iff_id_3815 _ rfl
  · exact mem_iff_id_3816 _ rfl
  · exact mem_iff_id_3817 _ rfl
  · exact mem_iff_id_3818 _ rfl
  · exact mem_iff_id_3819 _ rfl
  · exact mem_iff_id_3820 _ rfl
  · exact mem_iff_id_3821 _ rfl
  · exact mem_iff_id_3822 _ rfl
  · exact mem_iff_id_3823 _ rfl
  · exact mem_iff_id_3824 _ rfl
  · exact mem_iff_id_3825 _ rfl
  · exact mem_iff_id_3826 _ rfl
  · exact mem_iff_id_3827 _ rfl
  · exact mem_iff_id_3828 _ rfl
  · exact mem_iff_id_3829 _ rfl
  · exact mem_iff_id_3830 _ rfl
  · exact mem_iff_id_3831 _ rfl
  · exact mem_iff_id_3832 _ rfl
  · exact mem_iff_id_3833 _ rfl
  · exact mem_iff_id_3834 _ rfl
  · exact mem_iff_id_3835 _ rfl
  · exact mem_iff_id_3836 _ rfl
  · exact mem_iff_id_3837 _ rfl
  · exact mem_iff_id_3838 _ rfl
  · exact mem_iff_id_3839 _ rfl
  · exact mem_iff_id_3840 _ rfl
  · exact mem_iff_id_3841 _ rfl
  · exact mem_iff_id_3842 _ rfl
  · exact mem_iff_id_3843 _ rfl
  · exact mem_iff_id_3844 _ rfl
  · exact mem_iff_id_3845 _ rfl
  · exact mem_iff_id_3846 _ rfl
  · exact mem_iff_id_3847 _ rfl
  · exact mem_iff_id_3848 _ rfl
  · exact mem_iff_id_3849 _ rfl
  · exact mem_iff_id_3850 _ rfl
  · exact mem_iff_id_3851 _ rfl
  · exact mem_iff_id_3852 _ rfl
  · exact mem_iff_id_3853 _ rfl
  · exact mem_iff_id_3854 _ rfl
  · exact mem_iff_id_3855 _ rfl
  · exact mem_iff_id_3856 _ rfl
  · exact mem_iff_id_3857 _ rfl
  · exact mem_iff_id_3858 _ rfl
  · exact mem_iff_id_3859 _ rfl
  · exact mem_iff_id_3860 _ rfl
  · exact mem_iff_id_3861 _ rfl
  · exact mem_iff_id_3862 _ rfl
  · exact mem_iff_id_3863 _ rfl
  · exact mem_iff_id_3864 _ rfl
  · exact mem_iff_id_3865 _ rfl
  · exact mem_iff_id_3866 _ rfl
  · exact mem_iff_id_3867 _ rfl
  · exact mem_iff_id_3868 _ rfl
  · exact mem_iff_id_3869 _ rfl
  · exact mem_iff_id_3870 _ rfl
  · exact mem_iff_id_3871 _ rfl
  · exact mem_iff_id_3872 _ rfl
  · exact mem_iff_id_3873 _ rfl
  · exact mem_iff_id_3874 _ rfl
  · exact mem_iff_id_3875 _ rfl
  · exact mem_iff_id_3876 _ rfl
  · exact mem_iff_id_3877 _ rfl
  · exact mem_iff_id_3878 _ rfl
  · exact mem_iff_id_3879 _ rfl
  · exact mem_iff_id_3880 _ rfl
  · exact mem_iff_id_3881 _ rfl
  · exact mem_iff_id_3882 _ rfl
  · exact mem_iff_id_3883 _ rfl
  · exact mem_iff_id_3884 _ rfl
  · exact mem_iff_id_3885 _ rfl
  · exact mem_iff_id_3886 _ rfl
  · exact mem_iff_id_3887 _ rfl
  · exact mem_iff_id_3888 _ rfl
  · exact mem_iff_id_3889 _ rfl
  · exact mem_iff_id_3890 _ rfl
  · exact mem_iff_id_3891 _ rfl
  · exact mem_iff_id_3892 _ rfl
  · exact mem_iff_id_3893 _ rfl
  · exact mem_iff_id_3894 _ rfl
  · exact mem_iff_id_3895 _ rfl
  · exact mem_iff_id_3896 _ rfl
  · exact mem_iff_id_3897 _ rfl
  · exact mem_iff_id_3898 _ rfl
  · exact mem_iff_id_3899 _ rfl

theorem mem_iff_block42 (n : Fin 5011) (hlo : 4200 ≤ n.val) (hhi : n.val < 4300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_4200 _ rfl
  · exact mem_iff_id_4201 _ rfl
  · exact mem_iff_id_4202 _ rfl
  · exact mem_iff_id_4203 _ rfl
  · exact mem_iff_id_4204 _ rfl
  · exact mem_iff_id_4205 _ rfl
  · exact mem_iff_id_4206 _ rfl
  · exact mem_iff_id_4207 _ rfl
  · exact mem_iff_id_4208 _ rfl
  · exact mem_iff_id_4209 _ rfl
  · exact mem_iff_id_4210 _ rfl
  · exact mem_iff_id_4211 _ rfl
  · exact mem_iff_id_4212 _ rfl
  · exact mem_iff_id_4213 _ rfl
  · exact mem_iff_id_4214 _ rfl
  · exact mem_iff_id_4215 _ rfl
  · exact mem_iff_id_4216 _ rfl
  · exact mem_iff_id_4217 _ rfl
  · exact mem_iff_id_4218 _ rfl
  · exact mem_iff_id_4219 _ rfl
  · exact mem_iff_id_4220 _ rfl
  · exact mem_iff_id_4221 _ rfl
  · exact mem_iff_id_4222 _ rfl
  · exact mem_iff_id_4223 _ rfl
  · exact mem_iff_id_4224 _ rfl
  · exact mem_iff_id_4225 _ rfl
  · exact mem_iff_id_4226 _ rfl
  · exact mem_iff_id_4227 _ rfl
  · exact mem_iff_id_4228 _ rfl
  · exact mem_iff_id_4229 _ rfl
  · exact mem_iff_id_4230 _ rfl
  · exact mem_iff_id_4231 _ rfl
  · exact mem_iff_id_4232 _ rfl
  · exact mem_iff_id_4233 _ rfl
  · exact mem_iff_id_4234 _ rfl
  · exact mem_iff_id_4235 _ rfl
  · exact mem_iff_id_4236 _ rfl
  · exact mem_iff_id_4237 _ rfl
  · exact mem_iff_id_4238 _ rfl
  · exact mem_iff_id_4239 _ rfl
  · exact mem_iff_id_4240 _ rfl
  · exact mem_iff_id_4241 _ rfl
  · exact mem_iff_id_4242 _ rfl
  · exact mem_iff_id_4243 _ rfl
  · exact mem_iff_id_4244 _ rfl
  · exact mem_iff_id_4245 _ rfl
  · exact mem_iff_id_4246 _ rfl
  · exact mem_iff_id_4247 _ rfl
  · exact mem_iff_id_4248 _ rfl
  · exact mem_iff_id_4249 _ rfl
  · exact mem_iff_id_4250 _ rfl
  · exact mem_iff_id_4251 _ rfl
  · exact mem_iff_id_4252 _ rfl
  · exact mem_iff_id_4253 _ rfl
  · exact mem_iff_id_4254 _ rfl
  · exact mem_iff_id_4255 _ rfl
  · exact mem_iff_id_4256 _ rfl
  · exact mem_iff_id_4257 _ rfl
  · exact mem_iff_id_4258 _ rfl
  · exact mem_iff_id_4259 _ rfl
  · exact mem_iff_id_4260 _ rfl
  · exact mem_iff_id_4261 _ rfl
  · exact mem_iff_id_4262 _ rfl
  · exact mem_iff_id_4263 _ rfl
  · exact mem_iff_id_4264 _ rfl
  · exact mem_iff_id_4265 _ rfl
  · exact mem_iff_id_4266 _ rfl
  · exact mem_iff_id_4267 _ rfl
  · exact mem_iff_id_4268 _ rfl
  · exact mem_iff_id_4269 _ rfl
  · exact mem_iff_id_4270 _ rfl
  · exact mem_iff_id_4271 _ rfl
  · exact mem_iff_id_4272 _ rfl
  · exact mem_iff_id_4273 _ rfl
  · exact mem_iff_id_4274 _ rfl
  · exact mem_iff_id_4275 _ rfl
  · exact mem_iff_id_4276 _ rfl
  · exact mem_iff_id_4277 _ rfl
  · exact mem_iff_id_4278 _ rfl
  · exact mem_iff_id_4279 _ rfl
  · exact mem_iff_id_4280 _ rfl
  · exact mem_iff_id_4281 _ rfl
  · exact mem_iff_id_4282 _ rfl
  · exact mem_iff_id_4283 _ rfl
  · exact mem_iff_id_4284 _ rfl
  · exact mem_iff_id_4285 _ rfl
  · exact mem_iff_id_4286 _ rfl
  · exact mem_iff_id_4287 _ rfl
  · exact mem_iff_id_4288 _ rfl
  · exact mem_iff_id_4289 _ rfl
  · exact mem_iff_id_4290 _ rfl
  · exact mem_iff_id_4291 _ rfl
  · exact mem_iff_id_4292 _ rfl
  · exact mem_iff_id_4293 _ rfl
  · exact mem_iff_id_4294 _ rfl
  · exact mem_iff_id_4295 _ rfl
  · exact mem_iff_id_4296 _ rfl
  · exact mem_iff_id_4297 _ rfl
  · exact mem_iff_id_4298 _ rfl
  · exact mem_iff_id_4299 _ rfl

theorem mem_iff_block46 (n : Fin 5011) (hlo : 4600 ≤ n.val) (hhi : n.val < 4700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_4600 _ rfl
  · exact mem_iff_id_4601 _ rfl
  · exact mem_iff_id_4602 _ rfl
  · exact mem_iff_id_4603 _ rfl
  · exact mem_iff_id_4604 _ rfl
  · exact mem_iff_id_4605 _ rfl
  · exact mem_iff_id_4606 _ rfl
  · exact mem_iff_id_4607 _ rfl
  · exact mem_iff_id_4608 _ rfl
  · exact mem_iff_id_4609 _ rfl
  · exact mem_iff_id_4610 _ rfl
  · exact mem_iff_id_4611 _ rfl
  · exact mem_iff_id_4612 _ rfl
  · exact mem_iff_id_4613 _ rfl
  · exact mem_iff_id_4614 _ rfl
  · exact mem_iff_id_4615 _ rfl
  · exact mem_iff_id_4616 _ rfl
  · exact mem_iff_id_4617 _ rfl
  · exact mem_iff_id_4618 _ rfl
  · exact mem_iff_id_4619 _ rfl
  · exact mem_iff_id_4620 _ rfl
  · exact mem_iff_id_4621 _ rfl
  · exact mem_iff_id_4622 _ rfl
  · exact mem_iff_id_4623 _ rfl
  · exact mem_iff_id_4624 _ rfl
  · exact mem_iff_id_4625 _ rfl
  · exact mem_iff_id_4626 _ rfl
  · exact mem_iff_id_4627 _ rfl
  · exact mem_iff_id_4628 _ rfl
  · exact mem_iff_id_4629 _ rfl
  · exact mem_iff_id_4630 _ rfl
  · exact mem_iff_id_4631 _ rfl
  · exact mem_iff_id_4632 _ rfl
  · exact mem_iff_id_4633 _ rfl
  · exact mem_iff_id_4634 _ rfl
  · exact mem_iff_id_4635 _ rfl
  · exact mem_iff_id_4636 _ rfl
  · exact mem_iff_id_4637 _ rfl
  · exact mem_iff_id_4638 _ rfl
  · exact mem_iff_id_4639 _ rfl
  · exact mem_iff_id_4640 _ rfl
  · exact mem_iff_id_4641 _ rfl
  · exact mem_iff_id_4642 _ rfl
  · exact mem_iff_id_4643 _ rfl
  · exact mem_iff_id_4644 _ rfl
  · exact mem_iff_id_4645 _ rfl
  · exact mem_iff_id_4646 _ rfl
  · exact mem_iff_id_4647 _ rfl
  · exact mem_iff_id_4648 _ rfl
  · exact mem_iff_id_4649 _ rfl
  · exact mem_iff_id_4650 _ rfl
  · exact mem_iff_id_4651 _ rfl
  · exact mem_iff_id_4652 _ rfl
  · exact mem_iff_id_4653 _ rfl
  · exact mem_iff_id_4654 _ rfl
  · exact mem_iff_id_4655 _ rfl
  · exact mem_iff_id_4656 _ rfl
  · exact mem_iff_id_4657 _ rfl
  · exact mem_iff_id_4658 _ rfl
  · exact mem_iff_id_4659 _ rfl
  · exact mem_iff_id_4660 _ rfl
  · exact mem_iff_id_4661 _ rfl
  · exact mem_iff_id_4662 _ rfl
  · exact mem_iff_id_4663 _ rfl
  · exact mem_iff_id_4664 _ rfl
  · exact mem_iff_id_4665 _ rfl
  · exact mem_iff_id_4666 _ rfl
  · exact mem_iff_id_4667 _ rfl
  · exact mem_iff_id_4668 _ rfl
  · exact mem_iff_id_4669 _ rfl
  · exact mem_iff_id_4670 _ rfl
  · exact mem_iff_id_4671 _ rfl
  · exact mem_iff_id_4672 _ rfl
  · exact mem_iff_id_4673 _ rfl
  · exact mem_iff_id_4674 _ rfl
  · exact mem_iff_id_4675 _ rfl
  · exact mem_iff_id_4676 _ rfl
  · exact mem_iff_id_4677 _ rfl
  · exact mem_iff_id_4678 _ rfl
  · exact mem_iff_id_4679 _ rfl
  · exact mem_iff_id_4680 _ rfl
  · exact mem_iff_id_4681 _ rfl
  · exact mem_iff_id_4682 _ rfl
  · exact mem_iff_id_4683 _ rfl
  · exact mem_iff_id_4684 _ rfl
  · exact mem_iff_id_4685 _ rfl
  · exact mem_iff_id_4686 _ rfl
  · exact mem_iff_id_4687 _ rfl
  · exact mem_iff_id_4688 _ rfl
  · exact mem_iff_id_4689 _ rfl
  · exact mem_iff_id_4690 _ rfl
  · exact mem_iff_id_4691 _ rfl
  · exact mem_iff_id_4692 _ rfl
  · exact mem_iff_id_4693 _ rfl
  · exact mem_iff_id_4694 _ rfl
  · exact mem_iff_id_4695 _ rfl
  · exact mem_iff_id_4696 _ rfl
  · exact mem_iff_id_4697 _ rfl
  · exact mem_iff_id_4698 _ rfl
  · exact mem_iff_id_4699 _ rfl

theorem mem_iff_block50 (n : Fin 5011) (hlo : 5000 ≤ n.val) (hhi : n.val < 5011) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k
  · exact mem_iff_id_5000 _ rfl
  · exact mem_iff_id_5001 _ rfl
  · exact mem_iff_id_5002 _ rfl
  · exact mem_iff_id_5003 _ rfl
  · exact mem_iff_id_5004 _ rfl
  · exact mem_iff_id_5005 _ rfl
  · exact mem_iff_id_5006 _ rfl
  · exact mem_iff_id_5007 _ rfl
  · exact mem_iff_id_5008 _ rfl
  · exact mem_iff_id_5009 _ rfl
  · exact mem_iff_id_5010 _ rfl

end
end N11Formalization.EnergyTerminalResidualCensus
