import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FourthRadialC06
open C450RadialPacketKernel
def params : Params := ⟨((641363:ℚ)/250000),((677853:ℚ)/1000000),((1657997:ℚ)/2500000),((96:ℚ)/15625)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((82067:ℚ)/125000),((2009883719:ℚ)/10000000000),((394091729:ℚ)/625000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((82067:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((82067:ℚ)/125000),((168701:ℚ)/250000),((599727681:ℚ)/2500000000),((5437416843:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((82067:ℝ)/125000) ((168701:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((168701:ℚ)/250000),((341969:ℚ)/500000),((2557877333:ℚ)/10000000000),((990643641:ℚ)/2000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((168701:ℝ)/250000) ((341969:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((341969:ℚ)/500000),((43317:ℚ)/62500),((1349681463:ℚ)/5000000000),((4694124881:ℚ)/10000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((341969:ℝ)/500000) ((43317:ℝ)/62500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((43317:ℚ)/62500),((351103:ℚ)/500000),((2826277249:ℚ)/10000000000),((2210529971:ℚ)/5000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((43317:ℝ)/62500) ((351103:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((351103:ℚ)/500000),((706773:ℚ)/1000000),((22538773:ℚ)/78125000),((2065620517:ℚ)/5000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((351103:ℝ)/500000) ((706773:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((706773:ℚ)/1000000),((35567:ℚ)/50000),((2940767011:ℚ)/10000000000),((3978909103:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((706773:ℝ)/1000000) ((35567:ℝ)/50000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((35567:ℚ)/50000),((1427247:ℚ)/2000000),((148382453:ℚ)/500000000),((95521099:ℚ)/250000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((35567:ℝ)/50000) ((1427247:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((1427247:ℚ)/2000000),((715907:ℚ)/1000000),((2993880631:ℚ)/10000000000),((3739434743:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((1427247:ℝ)/2000000) ((715907:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((715907:ℚ)/1000000),((1436381:ℚ)/2000000),((603896459:ℚ)/2000000000),((3656300381:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((715907:ℝ)/1000000) ((1436381:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1436381:ℚ)/2000000),((360237:ℚ)/500000),((304447349:ℚ)/1000000000),((3571320181:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1436381:ℝ)/2000000) ((360237:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((360237:ℚ)/500000),((289103:ℚ)/400000),((95902269:ℚ)/312500000),((696871773:ℚ)/2000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((360237:ℝ)/500000) ((289103:ℝ)/400000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((289103:ℚ)/400000),((725041:ℚ)/1000000),((773174269:ℚ)/2500000000),((3395263981:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((289103:ℝ)/400000) ((725041:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((725041:ℚ)/1000000),((1454649:ℚ)/2000000),((97373857:ℚ)/312500000),((330386269:ℚ)/1000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((725041:ℝ)/1000000) ((1454649:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((1454649:ℚ)/2000000),((91201:ℚ)/125000),((3138687351:ℚ)/10000000000),((401244717:ℚ)/1250000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((1454649:ℝ)/2000000) ((91201:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((91201:ℚ)/125000),((1463783:ℚ)/2000000),((395110473:ℚ)/1250000000),((311332233:ℚ)/1000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((91201:ℝ)/125000) ((1463783:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((1463783:ℚ)/2000000),((29367:ℚ)/40000),((3182566929:ℚ)/10000000000),((3013693567:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((1463783:ℝ)/2000000) ((29367:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((29367:ℚ)/40000),((1472917:ℚ)/2000000),((3203750323:ℚ)/10000000000),((1455381917:ℚ)/5000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((29367:ℝ)/40000) ((1472917:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((1472917:ℚ)/2000000),((369371:ℚ)/500000),((1612223437:ℚ)/5000000000),((350521173:ℚ)/1250000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((1472917:ℝ)/2000000) ((369371:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((369371:ℚ)/500000),((743309:ℚ)/1000000),((102013381:ℚ)/312500000),((21547799:ℚ)/80000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((369371:ℝ)/500000) ((743309:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((743309:ℚ)/1000000),((186969:ℚ)/250000),((3302603081:ℚ)/10000000000),((1228774407:ℚ)/5000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((743309:ℝ)/1000000) ((186969:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((186969:ℚ)/250000),((75701:ℚ)/100000),((210866531:ℚ)/625000000),((219698699:ℚ)/1000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((186969:ℝ)/250000) ((75701:ℝ)/100000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((75701:ℚ)/100000),((11971:ℚ)/15625),((3438828851:ℚ)/10000000000),((310387787:ℚ)/2000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((75701:ℝ)/100000) ((11971:ℝ)/15625),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((168701:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((341969:ℝ)/500000) ((351103:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((168701:ℝ)/250000) ((351103:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((351103:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((706773:ℝ)/1000000) ((1427247:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node5_8 :
    ∀ r ∈ Set.Icc ((351103:ℝ)/500000) ((1427247:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 node6_8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((715907:ℝ)/1000000) ((360237:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node8_11 :
    ∀ r ∈ Set.Icc ((1427247:ℝ)/2000000) ((360237:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 node9_11
private theorem node5_11 :
    ∀ r ∈ Set.Icc ((351103:ℝ)/500000) ((360237:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_8 node8_11
private theorem node0_11 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((360237:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_11
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((289103:ℝ)/400000) ((1454649:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node11_14 :
    ∀ r ∈ Set.Icc ((360237:ℝ)/500000) ((1454649:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 node12_14
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((91201:ℝ)/125000) ((29367:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node14_17 :
    ∀ r ∈ Set.Icc ((1454649:ℝ)/2000000) ((29367:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 node15_17
private theorem node11_17 :
    ∀ r ∈ Set.Icc ((360237:ℝ)/500000) ((29367:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_14 node14_17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((1472917:ℝ)/2000000) ((743309:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node17_20 :
    ∀ r ∈ Set.Icc ((29367:ℝ)/40000) ((743309:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 node18_20
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((186969:ℝ)/250000) ((11971:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node20_23 :
    ∀ r ∈ Set.Icc ((743309:ℝ)/1000000) ((11971:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 node21_23
private theorem node17_23 :
    ∀ r ∈ Set.Icc ((29367:ℝ)/40000) ((11971:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_20 node20_23
private theorem node11_23 :
    ∀ r ∈ Set.Icc ((360237:ℝ)/500000) ((11971:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_17 node17_23
private theorem node0_23 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((11971:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_11 node11_23
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_23
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450FourthRadialC06
#check @N11Formalization.C450FourthRadialC06.bound
#print axioms N11Formalization.C450FourthRadialC06.params_valid
#print axioms N11Formalization.C450FourthRadialC06.bound
