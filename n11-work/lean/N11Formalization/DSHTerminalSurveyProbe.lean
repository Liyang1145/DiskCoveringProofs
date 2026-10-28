/-
  DSHTerminalSurveyProbe.lean -- type-pinning probe for the DSH-TERM-SURVEY deliverable.

  Purpose: upgrade the consumer-shape readings in
    evidence/dsh/terminals/survey/REPORT.md 4
  from "read from the committed source text" to "kernel-checked", per the project discipline
  that library facts must be probed rather than inferred (DEAD C‴ / C⁸).

  This file proves NOTHING about any terminal and adds no axiom, no `sorry`, no
  `native_decide`.  It is a `#check`/`#print axioms` probe only: its only content is
  signature printing plus one `example` stating the exact type of the two accepted
  consumers, so a type mismatch would be an elaboration error rather than a silent reading.

  Scope: survey evidence only.  Not root-imported, not a shared module.

  Gate:  & evidence/resume-lead/Invoke-LeanSerial.ps1 -File <abs path> -Log <fresh log>
  Read the real exit from <log>.result.json.
-/
import N11Formalization.Leaf284TreeBridge
import N11Formalization.Leaf4348TreeBridge
import N11Formalization.Leaf4348Radius
import N11Formalization.ResumeSchurEnergy

set_option autoImplicit false

namespace N11Formalization.DSHTerminalSurveyProbe

open N11Formalization

/-! ## 1. Network / cell / tree types (the terminal's input objects) -/

#check @ResumeNetwork.Edge
#check @ResumeNetwork.edgeLength
#check @ResumeNetwork.Feasible
#check @ResumeNetwork.feasibleSquares
#check @ResumeNetwork.V2
#check @ResumeNetwork.energy
#check @ResumeNetwork.oracle_le_feasible
#check @ResumeNetwork.oracle_le_of_geometric_witnesses
#check @ResumeNetwork.stress_lower_bound
#check @ResumeNetwork.dirichlet_le_oracle
#check @ResumeNetwork.edge_card
#check @FlashLeafSplit.Cell
#check @FlashLeafSplit.tlift
#check @DBMTreeKernel.matrix
#check @DBMTreeKernel.Node
#check @DBMTreeKernel.terminal_cover
#check @DBMSourceTree.data

/-! ## 2. Field/oracle layer, and its DIRECTION -/

#check @ResumeSchurEnergy.cosine_energy_le_oracle
#check @ResumeSchurEnergy.gram_le_oracle

/-! ## 3. Accepted terminal 284: exact consumer types -/

#check @FlashCosineLeaf284Oracle.source_energy_le_oracle
#check @FlashCosineLeaf284Oracle.mixture_weights
#check @FlashCosineLeaf284Oracle.mixture_identity
#check @FlashCosineLeaf284Oracle.mixture_le_oracle
#check @FlashCosineLeaf284Oracle.leaf284_oracle_gt
#check @FlashCosineLeaf284Oracle.leaf284_radius_gt
#check @Leaf284TreeBridge.leaf284_tree_oracle_gt
#check @Leaf284TreeBridge.leaf284_tree_radius_gt
#check @Leaf284TreeBridge.leaf284_cell_iff

/-! ## 4. Accepted terminal 4348: exact consumer types -/

#check @Leaf4348Oracle.leaf4348_oracle_gt
#check @Leaf4348Dispatch.hsafe_all
#check @Leaf4348Dispatch.leaf4348_oracle_gt
#check @Leaf4348Radius.leaf4348_radius_gt
#check @Leaf4348TreeBridge.leaf4348_tree_oracle_gt
#check @Leaf4348TreeBridge.leaf4348_tree_radius_gt
#check @Leaf4348TreeBridge.leaf4348_cell_iff
#check @Leaf4348TreeBridge.leaf4348_is_terminal

/-! ## 5. Type-identity assertions (a mismatch is an elaboration ERROR, not a silent reading)

Each `example` below is a fully written-out signature whose proof TERM is just the committed
theorem.  It elaborates iff the written type is exactly the theorem's type -- so the layout of
the consumer (which argument is free, which is a hypothesis, which side of `<` carries `T²`,
which side carries `V2`) is machine-checked rather than read off by eye.  No proposition is
proved here: the proof term is the existing theorem.
-/

-- The frozen threshold constant `T` used by both accepted terminals (a ℚ literal).
#check @FlashCosineLeaf284Bridge.T
#check @Leaf4348LP.T

/-- **284 oracle form**, written out.  Direction: `T² < V2`. -/
example :
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (fun i j => (FlashCosineLeaf284Bridge.dbm i j : ℝ))
        (FlashLeafSplit.tlift y) →
      (FlashCosineLeaf284Bridge.T : ℝ) ^ 2
        < ResumeNetwork.V2 (fun j => circleMap (FlashCosine.theta y j)) :=
  FlashCosineLeaf284Oracle.leaf284_oracle_gt

/-- **284 radius form**, written out.  Free `C Z r` appear ONLY as `Feasible` hypotheses;
conclusion is a radius (`T < r`), not a square. -/
example :
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (fun i j => (FlashCosineLeaf284Bridge.dbm i j : ℝ))
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        ResumeNetwork.Feasible (fun j => circleMap (FlashCosine.theta y j)) C Z r →
      (FlashCosineLeaf284Bridge.T : ℝ) < r :=
  FlashCosineLeaf284Oracle.leaf284_radius_gt

/-- **284 tree level**, written out: the cell is the emitted dispatcher literal
`DBMTreeKernel.matrix DBMSourceTree.data 4096 (284 : Fin 5011)`. -/
example :
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell
        (DBMTreeKernel.matrix DBMSourceTree.data 4096 (284 : Fin 5011))
        (FlashLeafSplit.tlift y) →
      (FlashCosineLeaf284Bridge.T : ℝ) ^ 2
        < ResumeNetwork.V2 (fun j => circleMap (FlashCosine.theta y j)) :=
  Leaf284TreeBridge.leaf284_tree_oracle_gt

/-- **284 tree radius level**, written out. -/
example :
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell
        (DBMTreeKernel.matrix DBMSourceTree.data 4096 (284 : Fin 5011))
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        ResumeNetwork.Feasible (fun j => circleMap (FlashCosine.theta y j)) C Z r →
      (FlashCosineLeaf284Bridge.T : ℝ) < r :=
  Leaf284TreeBridge.leaf284_tree_radius_gt

/-- **4348 dispatch oracle form**, written out: note `hsafe` is ABSENT (discharged by
`Leaf4348Dispatch.hsafe_all`), which is the difference from `Leaf4348Oracle.leaf4348_oracle_gt`. -/
example :
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (fun i j => (Leaf4348LP.dbm i j : ℝ))
        (FlashLeafSplit.tlift y) →
      (Leaf4348LP.T : ℝ) ^ 2
        < ResumeNetwork.V2 (fun j => circleMap (FlashCosine.theta y j)) :=
  Leaf4348Dispatch.leaf4348_oracle_gt

/-- **4348 radius form**, written out. -/
example :
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (fun i j => (Leaf4348LP.dbm i j : ℝ))
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        ResumeNetwork.Feasible (fun j => circleMap (FlashCosine.theta y j)) C Z r →
      (Leaf4348LP.T : ℝ) < r :=
  Leaf4348Radius.leaf4348_radius_gt

/-- **4348 tree level**, written out. -/
example :
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell
        (DBMTreeKernel.matrix DBMSourceTree.data 4096 (4348 : Fin 5011))
        (FlashLeafSplit.tlift y) →
      (Leaf4348LP.T : ℝ) ^ 2
        < ResumeNetwork.V2 (fun j => circleMap (FlashCosine.theta y j)) :=
  Leaf4348TreeBridge.leaf4348_tree_oracle_gt

/-- **Upper side**, for contrast: `Feasible` gives `V2 ≤ r²` (the opposite direction to the
terminals' conclusion).  Written out so the two directions are both machine-checked.
Note the binder form: the four network arguments are explicit (not implicit), so the proof
term is the bare theorem. -/
example (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ) :
    ResumeNetwork.Feasible U C Z r → ResumeNetwork.V2 U ≤ r ^ 2 :=
  ResumeNetwork.oracle_le_feasible

end N11Formalization.DSHTerminalSurveyProbe

#print axioms N11Formalization.ResumeNetwork.oracle_le_feasible
#print axioms N11Formalization.ResumeNetwork.stress_lower_bound
#print axioms N11Formalization.ResumeSchurEnergy.cosine_energy_le_oracle
#print axioms N11Formalization.FlashCosineLeaf284Oracle.leaf284_oracle_gt
#print axioms N11Formalization.Leaf284TreeBridge.leaf284_tree_radius_gt
#print axioms N11Formalization.Leaf4348Dispatch.leaf4348_oracle_gt
#print axioms N11Formalization.Leaf4348TreeBridge.leaf4348_tree_radius_gt
