import N11Formalization.C450GroupedPacketKernel
import N11Formalization.C450NormalizedInterface

/-! Exact closed radial joins and arbitrary-direction source consumption.
The family/coverage inputs remain explicit until actual source checks pay
them. No genericity, optimizer or finite-sample premise is introduced. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450GroupedClosedAssembly
open scoped Interval
open MeasureTheory
open C450GroupedPacketKernel C450NormalizedInterface

def CellBound (s : TenSeg)
    (h0 : |s.a1|+|s.a2|+|s.a3| ≤ s.a0)
    (h1 : |s.b1|+|s.b2|+|s.b3| ≤ s.b0)
    (Q : RatInterval) (lo hi : ℚ) : Prop :=
  ∀ (c : Point) (e : ℝ),
    ‖c‖ ∈ Set.Icc (lo:ℝ) (hi:ℝ) →
    RatInterval.Mem (offsetInterval s) e →
    RatInterval.Mem Q (c450Cq c e) →
    c450Outer (s.W0 h0) c+c450Inner (s.W1 h1) c e <
      Real.pi*((s.a0:ℝ)+(s.b0:ℝ))/10

theorem cell_of_packet (s : TenSeg)
    (h0 : |s.a1|+|s.a2|+|s.a3| ≤ s.a0)
    (h1 : |s.b1|+|s.b2|+|s.b3| ≤ s.b0) (p : Packet) (hp : Valid s p) :
    CellBound s h0 h1 p.Q p.lo p.hi := by
  intro c e hr he hq
  exact packet_bound s h0 h1 p hp c e ⟨hr.1,hr.2⟩ he hq

theorem cell_join {s : TenSeg}
    {h0 : |s.a1|+|s.a2|+|s.a3| ≤ s.a0}
    {h1 : |s.b1|+|s.b2|+|s.b3| ≤ s.b0}
    {Q : RatInterval} {lo mid hi : ℚ}
    (hl : CellBound s h0 h1 Q lo mid) (hr : CellBound s h0 h1 Q mid hi) :
    CellBound s h0 h1 Q lo hi := by
  intro c e hc he hq
  by_cases hm : ‖c‖ ≤ (mid:ℝ)
  · exact hl c e ⟨hc.1,hm⟩ he hq
  · exact hr c e ⟨(lt_of_not_ge hm).le,hc.2⟩ he hq

def DirectionsCover {n : ℕ} (Qs : Fin n → RatInterval) : Prop :=
  ∀ q ∈ Set.Icc (-1:ℝ) 1, ∃ i, RatInterval.Mem (Qs i) q

theorem normalized_of_cells {n : ℕ} (s : TenSeg)
    (h0 : |s.a1|+|s.a2|+|s.a3| ≤ s.a0)
    (h1 : |s.b1|+|s.b2|+|s.b3| ≤ s.b0)
    (heHi : s.eHi ≤ 7/50) (Qs : Fin n → RatInterval)
    (hcovers : DirectionsCover Qs)
    (hpaid : ∀ i, CellBound s h0 h1 (Qs i) (31/50) (69/50)) :
    PerDiskNormalized (s.W0 h0) (s.W1 h1) (s.eLo:ℝ) (s.eHi:ℝ) := by
  intro c e hc0 hc1 he0 heLo he1
  have he7 : e ≤ 7/50 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr heHi
    norm_num at hh
    exact he1.trans hh
  have hq := C450AngularMajorant.cq_bounds he0 he7 hc0
  obtain ⟨i,hi⟩ := hcovers (c450Cq c e) hq
  have hr : ‖c‖ ∈ Set.Icc ((31/50:ℚ):ℝ) ((69/50:ℚ):ℝ) := by
    norm_num
    exact ⟨by linarith,by linarith⟩
  have hh := hpaid i c e hr ⟨heLo,he1⟩ hi
  have hp := pair_canonical (s.W0 h0) (s.W1 h1) he0 he7 hc0 hc1
  unfold hubPt
  rw [hp]
  have htwo := mul_lt_mul_of_pos_left hh (by norm_num : (0:ℝ) < 2)
  have hRHS : 2*(Real.pi*((s.a0:ℝ)+(s.b0:ℝ))/10) =
      (2*Real.pi*(s.W0 h0).a0+2*Real.pi*(s.W1 h1).a0)/10 := by
    change _ = (2*Real.pi*(s.a0:ℝ)+2*Real.pi*(s.b0:ℝ))/10
    ring
  rw [hRHS] at htwo
  simpa only [mul_add] using htwo

end N11Formalization.C450GroupedClosedAssembly
#check @N11Formalization.C450GroupedClosedAssembly.cell_of_packet
#check @N11Formalization.C450GroupedClosedAssembly.cell_join
#check @N11Formalization.C450GroupedClosedAssembly.normalized_of_cells
#print axioms N11Formalization.C450GroupedClosedAssembly.cell_of_packet
#print axioms N11Formalization.C450GroupedClosedAssembly.cell_join
#print axioms N11Formalization.C450GroupedClosedAssembly.normalized_of_cells
