import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC50
open C450RadialPacketKernel
def params : Params := ⟨((262078071131:ℚ)/102400000000),((70487228069:ℚ)/102400000000),((2568071:ℚ)/4000000),((233:ℚ)/20000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((52633:ℚ)/80000),((2043421293:ℚ)/10000000000),((160683293:ℚ)/250000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((52633:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((52633:ℚ)/80000),((108299:ℚ)/160000),((2436563021:ℚ)/10000000000),((173173443:ℚ)/312500000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((52633:ℝ)/80000) ((108299:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((108299:ℚ)/160000),((219631:ℚ)/320000),((1298375999:ℚ)/5000000000),((2523828269:ℚ)/5000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((108299:ℝ)/160000) ((219631:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((219631:ℚ)/320000),((27833:ℚ)/40000),((342379893:ℚ)/1250000000),((4783426239:ℚ)/10000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((219631:ℝ)/320000) ((27833:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((27833:ℚ)/40000),((448361:ℚ)/640000),((1402216711:ℚ)/5000000000),((4504982637:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((27833:ℝ)/40000) ((448361:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((448361:ℚ)/640000),((225697:ℚ)/320000),((2866399471:ℚ)/10000000000),((4359581029:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((448361:ℝ)/640000) ((225697:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((225697:ℚ)/320000),((454427:ℚ)/640000),((2925190603:ℚ)/10000000000),((841898413:ℚ)/2000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((225697:ℝ)/320000) ((454427:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((454427:ℚ)/640000),((911887:ℚ)/1280000),((590693193:ℚ)/2000000000),((810838679:ℚ)/2000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((454427:ℝ)/640000) ((911887:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((911887:ℚ)/1280000),((22873:ℚ)/32000),((2981028619:ℚ)/10000000000),((3974399813:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((911887:ℝ)/1280000) ((22873:ℝ)/32000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((22873:ℚ)/32000),((917953:ℚ)/1280000),((3007902239:ℚ)/10000000000),((486632469:ℚ)/1250000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((22873:ℝ)/32000) ((917953:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((917953:ℚ)/1280000),((1838939:ℚ)/2560000),((1510543841:ℚ)/5000000000),((762014787:ℚ)/2000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((917953:ℝ)/1280000) ((1838939:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((1838939:ℚ)/2560000),((460493:ℚ)/640000),((758527283:ℚ)/2500000000),((3767929897:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((1838939:ℝ)/2560000) ((460493:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((460493:ℚ)/640000),((369001:ℚ)/512000),((152348459:ℚ)/500000000),((3725332141:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((460493:ℝ)/640000) ((369001:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((369001:ℚ)/512000),((924019:ℚ)/1280000),((3059670347:ℚ)/10000000000),((368226489:ℚ)/1000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((369001:ℝ)/512000) ((924019:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((924019:ℚ)/1280000),((1851071:ℚ)/2560000),((614443017:ℚ)/2000000000),((909677861:ℚ)/2500000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((924019:ℝ)/1280000) ((1851071:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((1851071:ℚ)/2560000),((231763:ℚ)/320000),((1542302889:ℚ)/5000000000),((3594654099:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((1851071:ℝ)/2560000) ((231763:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((231763:ℚ)/320000),((3711241:ℚ)/5120000),((618148817:ℚ)/2000000000),((221879629:ℚ)/625000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((231763:ℝ)/320000) ((3711241:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((3711241:ℚ)/5120000),((1857137:ℚ)/2560000),((1548422373:ℚ)/5000000000),((705516369:ℚ)/2000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((3711241:ℝ)/5120000) ((1857137:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((1857137:ℚ)/2560000),((3717307:ℚ)/5120000),((3102908041:ℚ)/10000000000),((876237841:ℚ)/2500000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((1857137:ℝ)/2560000) ((3717307:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((3717307:ℚ)/5120000),((186017:ℚ)/256000),((3108934247:ℚ)/10000000000),((3482179921:ℚ)/10000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((3717307:ℝ)/5120000) ((186017:ℝ)/256000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((186017:ℚ)/256000),((3723373:ℚ)/5120000),((1557461819:ℚ)/5000000000),((345926473:ℚ)/1000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((186017:ℝ)/256000) ((3723373:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((3723373:ℚ)/5120000),((1863203:ℚ)/2560000),((1560438241:ℚ)/5000000000),((343620291:ℚ)/1000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((3723373:ℝ)/5120000) ((1863203:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((1863203:ℚ)/2560000),((3729439:ℚ)/5120000),((625358609:ℚ)/2000000000),((682598297:ℚ)/2000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((1863203:ℝ)/2560000) ((3729439:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((3729439:ℚ)/5120000),((466559:ℚ)/640000),((3132673591:ℚ)/10000000000),((1694813689:ℚ)/5000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((3729439:ℝ)/5120000) ((466559:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((466559:ℚ)/640000),((747101:ℚ)/1024000),((3138518377:ℚ)/10000000000),((841526851:ℚ)/2500000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((466559:ℝ)/640000) ((747101:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((747101:ℚ)/1024000),((1869269:ℚ)/2560000),((3144327661:ℚ)/10000000000),((334242827:ℚ)/1000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((747101:ℝ)/1024000) ((1869269:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((1869269:ℚ)/2560000),((3741571:ℚ)/5120000),((630020339:ℚ)/2000000000),((663717313:ℚ)/2000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((1869269:ℝ)/2560000) ((3741571:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((3741571:ℚ)/5120000),((936151:ℚ)/1280000),((3155840727:ℚ)/10000000000),((658915751:ℚ)/2000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((3741571:ℝ)/5120000) ((936151:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((936151:ℚ)/1280000),((3747637:ℚ)/5120000),((790386251:ℚ)/2500000000),((1635200589:ℚ)/5000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((936151:ℝ)/1280000) ((3747637:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((3747637:ℚ)/5120000),((375067:ℚ)/512000),((316721477:ℚ)/1000000000),((811512509:ℚ)/2500000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((3747637:ℝ)/5120000) ((375067:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((375067:ℚ)/512000),((3753703:ℚ)/5120000),((396606283:ℚ)/1250000000),((322152139:ℚ)/1000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((375067:ℝ)/512000) ((3753703:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((3753703:ℚ)/5120000),((58699:ℚ)/80000),((794612931:ℚ)/2500000000),((799202787:ℚ)/2500000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((3753703:ℝ)/5120000) ((58699:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((58699:ℚ)/80000),((1881401:ℚ)/2560000),((127582139:ℚ)/400000000),((3171915063:ℚ)/10000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((58699:ℝ)/80000) ((1881401:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((1881401:ℚ)/2560000),((942217:ℚ)/1280000),((3200521861:ℚ)/10000000000),((3121547527:ℚ)/10000000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((1881401:ℝ)/2560000) ((942217:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((942217:ℚ)/1280000),((1887467:ℚ)/2560000),((3211358679:ℚ)/10000000000),((614076257:ℚ)/2000000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((942217:ℝ)/1280000) ((1887467:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((1887467:ℚ)/2560000),((3781:ℚ)/5120),((40275821:ℚ)/125000000),((754593921:ℚ)/2500000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((1887467:ℝ)/2560000) ((3781:ℝ)/5120),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((3781:ℚ)/5120),((1893533:ℚ)/2560000),((129305783:ℚ)/400000000),((46335727:ℚ)/156250000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((3781:ℝ)/5120) ((1893533:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((1893533:ℚ)/2560000),((948283:ℚ)/1280000),((1621548517:ℚ)/5000000000),((2911665633:ℚ)/10000000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((1893533:ℝ)/2560000) ((948283:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((948283:ℚ)/1280000),((237829:ℚ)/320000),((163181457:ℚ)/500000000),((1428430151:ℚ)/5000000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((948283:ℝ)/1280000) ((237829:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((237829:ℚ)/320000),((954349:ℚ)/1280000),((328367461:ℚ)/1000000000),((343007399:ℚ)/1250000000)⟩
theorem valid39 : Valid params packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((237829:ℝ)/320000) ((954349:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((954349:ℚ)/1280000),((478691:ℚ)/640000),((412905687:ℚ)/1250000000),((656636259:ℚ)/2500000000)⟩
theorem valid40 : Valid params packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((954349:ℝ)/1280000) ((478691:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((478691:ℚ)/640000),((120431:ℚ)/160000),((26728073:ℚ)/80000000),((2503653937:ℚ)/10000000000)⟩
theorem valid41 : Valid params packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((478691:ℝ)/640000) ((120431:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((120431:ℚ)/160000),((48779:ℚ)/64000),((3411316933:ℚ)/10000000000),((1119080359:ℚ)/5000000000)⟩
theorem valid42 : Valid params packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((120431:ℝ)/160000) ((48779:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((48779:ℚ)/64000),((15433:ℚ)/20000),((868791093:ℚ)/2500000000),((31619267:ℚ)/200000000)⟩
theorem valid43 : Valid params packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((48779:ℝ)/64000) ((15433:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((108299:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((219631:ℝ)/320000) ((448361:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((108299:ℝ)/160000) ((448361:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((448361:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((225697:ℝ)/320000) ((911887:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node5_8 :
    ∀ r ∈ Set.Icc ((448361:ℝ)/640000) ((911887:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 node6_8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((22873:ℝ)/32000) ((1838939:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node8_11 :
    ∀ r ∈ Set.Icc ((911887:ℝ)/1280000) ((1838939:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 node9_11
private theorem node5_11 :
    ∀ r ∈ Set.Icc ((448361:ℝ)/640000) ((1838939:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_8 node8_11
private theorem node0_11 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1838939:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((1838939:ℝ)/2560000) ((369001:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((924019:ℝ)/1280000) ((231763:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node13_16 :
    ∀ r ∈ Set.Icc ((369001:ℝ)/512000) ((231763:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 node14_16
private theorem node11_16 :
    ∀ r ∈ Set.Icc ((1838939:ℝ)/2560000) ((231763:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_16
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((3711241:ℝ)/5120000) ((3717307:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node16_19 :
    ∀ r ∈ Set.Icc ((231763:ℝ)/320000) ((3717307:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 node17_19
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((186017:ℝ)/256000) ((1863203:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node19_22 :
    ∀ r ∈ Set.Icc ((3717307:ℝ)/5120000) ((1863203:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 node20_22
private theorem node16_22 :
    ∀ r ∈ Set.Icc ((231763:ℝ)/320000) ((1863203:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_19 node19_22
private theorem node11_22 :
    ∀ r ∈ Set.Icc ((1838939:ℝ)/2560000) ((1863203:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_16 node16_22
private theorem node0_22 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1863203:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_11 node11_22
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((1863203:ℝ)/2560000) ((466559:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((747101:ℝ)/1024000) ((3741571:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node24_27 :
    ∀ r ∈ Set.Icc ((466559:ℝ)/640000) ((3741571:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 node25_27
private theorem node22_27 :
    ∀ r ∈ Set.Icc ((1863203:ℝ)/2560000) ((3741571:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_24 node24_27
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((936151:ℝ)/1280000) ((375067:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node27_30 :
    ∀ r ∈ Set.Icc ((3741571:ℝ)/5120000) ((375067:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 node28_30
private theorem node31_33 :
    ∀ r ∈ Set.Icc ((3753703:ℝ)/5120000) ((1881401:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 leaf32
private theorem node30_33 :
    ∀ r ∈ Set.Icc ((375067:ℝ)/512000) ((1881401:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 node31_33
private theorem node27_33 :
    ∀ r ∈ Set.Icc ((3741571:ℝ)/5120000) ((1881401:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node27_30 node30_33
private theorem node22_33 :
    ∀ r ∈ Set.Icc ((1863203:ℝ)/2560000) ((1881401:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_27 node27_33
private theorem node33_35 :
    ∀ r ∈ Set.Icc ((1881401:ℝ)/2560000) ((1887467:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf33 leaf34
private theorem node36_38 :
    ∀ r ∈ Set.Icc ((3781:ℝ)/5120) ((948283:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf36 leaf37
private theorem node35_38 :
    ∀ r ∈ Set.Icc ((1887467:ℝ)/2560000) ((948283:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf35 node36_38
private theorem node33_38 :
    ∀ r ∈ Set.Icc ((1881401:ℝ)/2560000) ((948283:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node33_35 node35_38
private theorem node39_41 :
    ∀ r ∈ Set.Icc ((237829:ℝ)/320000) ((478691:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf39 leaf40
private theorem node38_41 :
    ∀ r ∈ Set.Icc ((948283:ℝ)/1280000) ((478691:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf38 node39_41
private theorem node42_44 :
    ∀ r ∈ Set.Icc ((120431:ℝ)/160000) ((15433:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf42 leaf43
private theorem node41_44 :
    ∀ r ∈ Set.Icc ((478691:ℝ)/640000) ((15433:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf41 node42_44
private theorem node38_44 :
    ∀ r ∈ Set.Icc ((948283:ℝ)/1280000) ((15433:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node38_41 node41_44
private theorem node33_44 :
    ∀ r ∈ Set.Icc ((1881401:ℝ)/2560000) ((15433:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node33_38 node38_44
private theorem node22_44 :
    ∀ r ∈ Set.Icc ((1863203:ℝ)/2560000) ((15433:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_33 node33_44
private theorem node0_44 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((15433:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_22 node22_44
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_44
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC50
#check @N11Formalization.C450SixthRadialC50.bound
#print axioms N11Formalization.C450SixthRadialC50.params_valid
#print axioms N11Formalization.C450SixthRadialC50.params_sum
#print axioms N11Formalization.C450SixthRadialC50.bound
