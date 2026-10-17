import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450GroupedPacketImportedAudit
open C450GroupedPacketKernel C450GroupedAmplitude

def seventh : TenSeg :=
  ⟨1/50,3/125,638997/250000,-3923/250000,-913/100000,-1523/500000,
    694981/1000000,-88593/500000,22417/1000000,253/125000⟩
def last : TenSeg :=
  ⟨17/125,7/50,26531/12500,-49061/100000,28973/500000,59453/500000,
    640343/500000,-856119/1000000,291739/1000000,-33207/250000⟩
theorem seventh_source : c450Segs[6]? = some seventh := by decide +kernel
theorem last_source : c450Segs[35]? = some last := by decide +kernel
theorem seventh_nn0 : |seventh.a1|+|seventh.a2|+|seventh.a3| ≤ seventh.a0 := by decide +kernel
theorem seventh_nn1 : |seventh.b1|+|seventh.b2|+|seventh.b3| ≤ seventh.b0 := by decide +kernel
theorem last_nn0 : |last.a1|+|last.a2|+|last.a3| ≤ last.a0 := by decide +kernel
theorem last_nn1 : |last.b1|+|last.b2|+|last.b3| ≤ last.b0 := by decide +kernel

/-- First actual pilot packets only: NOT complete606/672 or segment payment. -/
def pilot7 : Packet :=
  ⟨31/50,103/160,-1,-15/16,79838867/125000000,6677500003/10000000000,
    -1,-229916601/257500000,9864186891/10000000000,1,
    1649979683/10000000000,2863793171/5000000000,
    443728287538337666499853252917/33153125000000000000000000000000,
    11337522555895696640539/57760000000000000000000⟩
def pilot36 : Packet :=
  ⟨31/50,103/160,-1,-15/16,745691111/1000000000,7837500003/10000000000,
    -1,-1789073333/2060000000,9864186891/10000000000,1,
    1649979683/10000000000,1943546399/10000000000,
    44817576498809790912874987394569436280614466041184559/
      81954525000000000000000000000000000000000000000000000,
    640343/500000⟩
theorem valid7 : Valid seventh pilot7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
theorem valid36 : Valid last pilot36 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel

theorem pilot7_continuum (c : Point) (e : ℝ)
    (hr : ‖c‖ ∈ Set.Icc ((31:ℝ)/50) (103/160))
    (he : e ∈ Set.Icc ((1:ℝ)/50) (3/125))
    (hq : c450Cq c e ∈ Set.Icc (-1:ℝ) (-15/16)) :
    c450Outer (seventh.W0 seventh_nn0) c+c450Inner (seventh.W1 seventh_nn1) c e <
      Real.pi*((seventh.a0:ℝ)+(seventh.b0:ℝ))/10 := by
  apply packet_bound seventh seventh_nn0 seventh_nn1 pilot7 valid7 c e
  · simpa only [pilot7,Packet.R,RatInterval.Mem,RatInterval.toSet,
      Set.mem_setOf_eq,Set.mem_Icc,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hr
  · simpa only [seventh,offsetInterval,RatInterval.Mem,RatInterval.toSet,
      Set.mem_setOf_eq,Set.mem_Icc,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using he
  · simpa only [pilot7,Packet.Q,RatInterval.Mem,RatInterval.toSet,
      Set.mem_setOf_eq,Set.mem_Icc,Rat.cast_div,Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat] using hq

theorem pilot36_continuum (c : Point) (e : ℝ)
    (hr : ‖c‖ ∈ Set.Icc ((31:ℝ)/50) (103/160))
    (he : e ∈ Set.Icc ((17:ℝ)/125) (7/50))
    (hq : c450Cq c e ∈ Set.Icc (-1:ℝ) (-15/16)) :
    c450Outer (last.W0 last_nn0) c+c450Inner (last.W1 last_nn1) c e <
      Real.pi*((last.a0:ℝ)+(last.b0:ℝ))/10 := by
  apply packet_bound last last_nn0 last_nn1 pilot36 valid36 c e
  · simpa only [pilot36,Packet.R,RatInterval.Mem,RatInterval.toSet,
      Set.mem_setOf_eq,Set.mem_Icc,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hr
  · simpa only [last,offsetInterval,RatInterval.Mem,RatInterval.toSet,
      Set.mem_setOf_eq,Set.mem_Icc,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using he
  · simpa only [pilot36,Packet.Q,RatInterval.Mem,RatInterval.toSet,
      Set.mem_setOf_eq,Set.mem_Icc,Rat.cast_div,Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat] using hq

example : |pilot36.p1| = last.b0 := by decide +kernel
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : C450SixthSegment.remainingSegs.length = 30 := C450SixthSegment.remaining_count
example : EnergyTerminalBatchB11.paidIDs.card = 310 := EnergyTerminalBatchB11.paid_count
end N11Formalization.C450GroupedPacketImportedAudit
#check @N11Formalization.C450GroupedPacketKernel.Valid
#check @N11Formalization.C450GroupedPacketKernel.packet_bound
#check @N11Formalization.C450GroupedPacketKernel.packet_integrals
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.C450GroupedAmplitude.lower2Q_cast
#print axioms N11Formalization.C450GroupedAmplitude.upper2Q_cast
#print axioms N11Formalization.C450GroupedAmplitude.lower3Q_cast
#print axioms N11Formalization.C450GroupedAmplitude.upper3Q_cast
#print axioms N11Formalization.C450GroupedAmplitude.range2_mem
#print axioms N11Formalization.C450GroupedAmplitude.range3_mem
#print axioms N11Formalization.C450GroupedAmplitude.squareThird_mem
#print axioms N11Formalization.C450GroupedAmplitude.amplitude_mem
#print axioms N11Formalization.C450GroupedAmplitude.actual_amplitude_le
#print axioms N11Formalization.C450GroupedAmplitude.arc_upper
#print axioms N11Formalization.C450GroupedPacketKernel.actual_geometry
#print axioms N11Formalization.C450GroupedPacketKernel.cap_lt_actual
#print axioms N11Formalization.C450GroupedPacketKernel.packet_bound
#print axioms N11Formalization.C450GroupedPacketKernel.packet_integrals
#print axioms N11Formalization.C450GroupedPacketImportedAudit.seventh_source
#print axioms N11Formalization.C450GroupedPacketImportedAudit.last_source
#print axioms N11Formalization.C450GroupedPacketImportedAudit.valid7
#print axioms N11Formalization.C450GroupedPacketImportedAudit.valid36
#print axioms N11Formalization.C450GroupedPacketImportedAudit.pilot7_continuum
#print axioms N11Formalization.C450GroupedPacketImportedAudit.pilot36_continuum
