import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ThirdRadialNeg1
open C450RadialPacketKernel
def params : Params := ⟨((641363:ℚ)/250000),((338529:ℚ)/500000),((744823:ℚ)/1000000),((-1743:ℚ)/500000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((1308257:ℚ)/2000000),((1949147203:ℚ)/10000000000),((3043637607:ℚ)/5000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1308257:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((1308257:ℚ)/2000000),((2684771:ℚ)/4000000),((2330385881:ℚ)/10000000000),((262541601:ℚ)/500000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((1308257:ℝ)/2000000) ((2684771:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((2684771:ℚ)/4000000),((5437799:ℚ)/8000000),((155433697:ℚ)/625000000),((1195986079:ℚ)/2500000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((2684771:ℝ)/4000000) ((5437799:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((5437799:ℚ)/8000000),((688257:ℚ)/1000000),((1313378673:ℚ)/5000000000),((2267015299:ℚ)/5000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((5437799:ℝ)/8000000) ((688257:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((688257:ℚ)/1000000),((11080369:ℚ)/16000000),((538259223:ℚ)/2000000000),((213529109:ℚ)/500000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((688257:ℝ)/1000000) ((11080369:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((11080369:ℚ)/16000000),((5574313:ℚ)/8000000),((2752634401:ℚ)/10000000000),((4132975669:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((11080369:ℝ)/16000000) ((5574313:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((5574313:ℚ)/8000000),((11216883:ℚ)/16000000),((281100979:ℚ)/1000000000),((997727221:ℚ)/2500000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((5574313:ℝ)/8000000) ((11216883:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((11216883:ℚ)/16000000),((22502023:ℚ)/32000000),((354894049:ℚ)/1250000000),((3843885949:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((11216883:ℝ)/16000000) ((22502023:ℝ)/32000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((22502023:ℚ)/32000000),((564257:ℚ)/800000),((143331511:ℚ)/500000000),((3768334981:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((22502023:ℝ)/32000000) ((564257:ℝ)/800000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((564257:ℚ)/800000),((22638537:ℚ)/32000000),((144673273:ℚ)/500000000),((3691313299:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((564257:ℝ)/800000) ((22638537:ℝ)/32000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((22638537:ℚ)/32000000),((11353397:ℚ)/16000000),((2919679011:ℚ)/10000000000),((3612726661:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((22638537:ℝ)/32000000) ((11353397:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((11353397:ℚ)/16000000),((9096369:ℚ)/12800000),((1466279429:ℚ)/5000000000),((3532470441:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((11353397:ℝ)/16000000) ((9096369:ℝ)/12800000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((9096369:ℚ)/12800000),((22775051:ℚ)/32000000),((294529059:ℚ)/1000000000),((3491680297:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((9096369:ℝ)/12800000) ((22775051:ℝ)/32000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((22775051:ℚ)/32000000),((45618359:ℚ)/64000000),((2957876503:ℚ)/10000000000),((215651747:ℚ)/625000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((22775051:ℝ)/32000000) ((45618359:ℝ)/64000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((45618359:ℚ)/64000000),((5710827:ℚ)/8000000),((297031883:ℚ)/1000000000),((3408696603:ℚ)/10000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((45618359:ℝ)/64000000) ((5710827:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((5710827:ℚ)/8000000),((45754873:ℚ)/64000000),((2982619743:ℚ)/10000000000),((841617103:ℚ)/2500000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((5710827:ℝ)/8000000) ((45754873:ℝ)/64000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((45754873:ℚ)/64000000),((4582313:ℚ)/6400000),((2994781357:ℚ)/10000000000),((1661862209:ℚ)/5000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((45754873:ℝ)/64000000) ((4582313:ℝ)/6400000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((4582313:ℚ)/6400000),((45891387:ℚ)/64000000),((751701433:ℚ)/2500000000),((1640222217:ℚ)/5000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((4582313:ℝ)/6400000) ((45891387:ℝ)/64000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((45891387:ℚ)/64000000),((11489911:ℚ)/16000000),((3018694873:ℚ)/10000000000),((647321387:ℚ)/2000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((45891387:ℝ)/64000000) ((11489911:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((11489911:ℚ)/16000000),((23048079:ℚ)/32000000),((3042075217:ℚ)/10000000000),((1596094463:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((11489911:ℝ)/16000000) ((23048079:ℝ)/32000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((23048079:ℚ)/32000000),((1444771:ℚ)/2000000),((3064937433:ℚ)/10000000000),((387688899:ℚ)/1250000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((23048079:ℝ)/32000000) ((1444771:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((1444771:ℚ)/2000000),((23184593:ℚ)/32000000),((3087295821:ℚ)/10000000000),((601638397:ℚ)/2000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((1444771:ℝ)/2000000) ((23184593:ℝ)/32000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((23184593:ℚ)/32000000),((465057:ℚ)/640000),((3109163993:ℚ)/10000000000),((2911977153:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((23184593:ℝ)/32000000) ((465057:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((465057:ℚ)/640000),((5847341:ℚ)/8000000),((787870239:ℚ)/2500000000),((2812569319:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((465057:ℝ)/640000) ((5847341:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((5847341:ℚ)/8000000),((11762939:ℚ)/16000000),((797996271:ℚ)/2500000000),((2602698913:ℚ)/10000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((5847341:ℝ)/8000000) ((11762939:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((11762939:ℚ)/16000000),((2957799:ℚ)/4000000),((3230764693:ℚ)/10000000000),((2374804309:ℚ)/10000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((11762939:ℝ)/16000000) ((2957799:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((2957799:ℚ)/4000000),((1196771:ℚ)/1600000),((165173367:ℚ)/500000000),((2123086899:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((2957799:ℝ)/4000000) ((1196771:ℝ)/1600000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((1196771:ℚ)/1600000),((378257:ℚ)/500000),((3370161477:ℚ)/10000000000),((299967319:ℚ)/2000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((1196771:ℝ)/1600000) ((378257:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((1308257:ℝ)/2000000) ((5437799:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((5437799:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((5437799:ℝ)/8000000) ((11080369:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((11080369:ℝ)/16000000) ((11216883:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node3_7 :
    ∀ r ∈ Set.Icc ((5437799:ℝ)/8000000) ((11216883:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node3_5 node5_7
private theorem node0_7 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((11216883:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_7
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((22502023:ℝ)/32000000) ((22638537:ℝ)/32000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node7_10 :
    ∀ r ∈ Set.Icc ((11216883:ℝ)/16000000) ((22638537:ℝ)/32000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 node8_10
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((22638537:ℝ)/32000000) ((9096369:ℝ)/12800000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((9096369:ℝ)/12800000) ((45618359:ℝ)/64000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node10_14 :
    ∀ r ∈ Set.Icc ((22638537:ℝ)/32000000) ((45618359:ℝ)/64000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_12 node12_14
private theorem node7_14 :
    ∀ r ∈ Set.Icc ((11216883:ℝ)/16000000) ((45618359:ℝ)/64000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_10 node10_14
private theorem node0_14 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((45618359:ℝ)/64000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_7 node7_14
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((5710827:ℝ)/8000000) ((4582313:ℝ)/6400000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node14_17 :
    ∀ r ∈ Set.Icc ((45618359:ℝ)/64000000) ((4582313:ℝ)/6400000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 node15_17
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((4582313:ℝ)/6400000) ((11489911:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((11489911:ℝ)/16000000) ((1444771:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node17_21 :
    ∀ r ∈ Set.Icc ((4582313:ℝ)/6400000) ((1444771:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_19 node19_21
private theorem node14_21 :
    ∀ r ∈ Set.Icc ((45618359:ℝ)/64000000) ((1444771:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node14_17 node17_21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((23184593:ℝ)/32000000) ((5847341:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node21_24 :
    ∀ r ∈ Set.Icc ((1444771:ℝ)/2000000) ((5847341:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 node22_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((5847341:ℝ)/8000000) ((2957799:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((2957799:ℝ)/4000000) ((378257:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((5847341:ℝ)/8000000) ((378257:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node24_26 node26_28
private theorem node21_28 :
    ∀ r ∈ Set.Icc ((1444771:ℝ)/2000000) ((378257:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_24 node24_28
private theorem node14_28 :
    ∀ r ∈ Set.Icc ((45618359:ℝ)/64000000) ((378257:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node14_21 node21_28
private theorem node0_28 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((378257:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_14 node14_28
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_28
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450ThirdRadialNeg1
#check @N11Formalization.C450ThirdRadialNeg1.bound
#print axioms N11Formalization.C450ThirdRadialNeg1.params_valid
#print axioms N11Formalization.C450ThirdRadialNeg1.bound
