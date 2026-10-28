import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((414592407:ℚ)/625000000),((1707824441:ℚ)/2500000000),((-1371824441:ℚ)/2480000000),((-2851331663:ℚ)/6318750000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((203933119:ℚ)/400000000),((523531316256348506966509382263729668487846690353450160553:ℚ)/2706667263200000000000000000000000000000000000000000000000),((420640116742230995341:ℚ)/1500000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6752966367:ℚ)/10000000000),((1390148527:ℚ)/2000000000),((-1121348527:ℚ)/2022000000),((-46696697303:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((953250727:ℚ)/2000000000),((26503337357551249746453340932785065039635458096747347271:ℚ)/137037027344737500000000000000000000000000000000000000000),((38493170752868173667823061:ℚ)/138624000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1374485351:ℚ)/2000000000),((876306933:ℚ)/1250000000),((-708306933:ℚ)/1287500000),((-1364909737:ℚ)/2970000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((441137251:ℚ)/1000000000),((518160108932227538063356705124886154843127307393330647:ℚ)/2723647391510009765625000000000000000000000000000000000),((508116264216611347724183:ℚ)/1848320000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((55457177:ℚ)/80000000),((3535081061:ℚ)/5000000000),((-2863081061:ℚ)/5197500000),((-386474593:ℚ)/839200000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4223586879:ℚ)/10000000000),((347973636363875167650855917818376899752919405797661120189:ℚ)/1828860437465716552734375000000000000000000000000000000000),((808855240077195430807:ℚ)/2957312000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((3495930593:ℚ)/5000000000),((3564931389:ℚ)/5000000000),((-2892931389:ℚ)/5245000000),((-24423375337:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2013812217:ℚ)/5000000000),((2633843149406122186141966844055364212789407260589035543581:ℚ)/13841251485167382812500000000000000000000000000000000000000),((8707415034593244582447:ℚ)/32000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((705156911:ℚ)/1000000000),((7189557593:ℚ)/10000000000),((-5845557593:ℚ)/10585000000),((-4938412199:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3822223157:ℚ)/10000000000),((9566417398072212641605286329232369895281528461190915737:ℚ)/50267788012744140625000000000000000000000000000000000000),((125083390696200049347943:ℚ)/462080000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((3555635531:ℚ)/5000000000),((360970143:ℚ)/500000000),((-97923381:ℚ)/178000000),((-24960719779:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((1802882803:ℚ)/5000000000),((478704519346779090623419384091310097829840912457703053:ℚ)/2535228381228320312500000000000000000000000000000000000),((3110714580545733274861263:ℚ)/11552000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((7141119849:ℚ)/10000000000),((1812311681:ℚ)/2500000000),((-1476311681:ℚ)/2681875000),((-50190078641:ℚ)/107750000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3492750999:ℚ)/10000000000),((33039202714712349512279307104930618120360942816178311239:ℚ)/174960569491614472866058349609375000000000000000000000000),((37230002197676521657182949:ℚ)/138624000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((3585483601:ℚ)/5000000000),((3639544603:ℚ)/5000000000),((-2967544603:ℚ)/5387500000),((-25229352409:ℚ)/54112500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3376120843:ℚ)/10000000000),((11844420344570656153826859848971799404000443686063082433:ℚ)/62717190558815002441406250000000000000000000000000000000),((3094266246650943114446183:ℚ)/11552000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7200813141:ℚ)/10000000000),((3654465161:ℚ)/5000000000),((-229420397:ℚ)/416250000),((-50727318269:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((813871483:ℚ)/2500000000),((75519933811302299962669880125679122791500643420936137:ℚ)/399850478640747070312500000000000000000000000000000000),((37032153220980942542189869:ℚ)/138624000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1807664421:ℚ)/2500000000),((7368608531:ℚ)/10000000000),((-6024608531:ℚ)/10870000000),((-12748979789:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((782595663:ℚ)/2500000000),((51033651782063901962893461707574737055200904295480128509923:ℚ)/268091732245540234375000000000000000000000000000000000000000),((2308304809701958597130509:ℚ)/8664000000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((28477901:ℚ)/39062500),((1857070373:ℚ)/2500000000),((-1521070373:ℚ)/2741250000),((-201301109:ℚ)/432031250),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2864406319:ℚ)/10000000000),((1722232281777562952539363466553834446710277208198759893:ℚ)/9046640393251848220825195312500000000000000000000000000),((93418428369070935929:ℚ)/352539062500000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((3675011131:ℚ)/5000000000),((7547612207:ℚ)/10000000000),((-6203612207:ℚ)/11060000000),((-26035100179:ℚ)/56250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((160744649:ℚ)/625000000),((4787238422223151040203895138483781592997511360288917:ℚ)/24772320849609375000000000000000000000000000000000000),((3044452171961402324578863:ℚ)/11552000000000000000000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((298774637:ℚ)/400000000),((1533384699:ℚ)/2000000000),((-140509411:ℚ)/250000000),((-2125771733:ℚ)/4576000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((232097521:ℚ)/1250000000),((570762000022033022863430369250618010210601205186683:ℚ)/2954101562500000000000000000000000000000000000000000),((19269450975215184543327:ℚ)/73932800000000000000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((3794344863:ℚ)/5000000000),((1724163561:ℚ)/2000000000),((-1455363561:ℚ)/2288000000),((-27109103767:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((545630503:ℚ)/10000000000),((2436719953085890394353462723235380177450991667195671:ℚ)/10600761600000000000000000000000000000000000000000000),((8930814725653449938272981:ℚ)/34656000000000000000000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((8542670767:ℚ)/10000000000),((105263771:ℚ)/100000000),((-91823771:ℚ)/129600000),((-62804036903:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((882987343179770913901221760914454170926341671643:ℚ)/3401222400000000000000000000000000000000000000000),((1029677:ℚ)/4000000)⟩
theorem valid15 : Valid source23 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((5224176829:ℚ)/5000000000),((14332891571:ℚ)/10000000000),((-12988891571:ℚ)/16000000000),((-39977591461:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((266307221422744806881382864255889274958975349138123683707:ℚ)/846400000000000000000000000000000000000000000000000000000),((1029677:ℚ)/4000000)⟩
theorem valid16 : Valid source23 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC07
#check @N11Formalization.C450Source23GroupedC07.bound
#print axioms N11Formalization.C450Source23GroupedC07.valid0
#print axioms N11Formalization.C450Source23GroupedC07.valid1
#print axioms N11Formalization.C450Source23GroupedC07.valid2
#print axioms N11Formalization.C450Source23GroupedC07.valid3
#print axioms N11Formalization.C450Source23GroupedC07.valid4
#print axioms N11Formalization.C450Source23GroupedC07.valid5
#print axioms N11Formalization.C450Source23GroupedC07.valid6
#print axioms N11Formalization.C450Source23GroupedC07.valid7
#print axioms N11Formalization.C450Source23GroupedC07.valid8
#print axioms N11Formalization.C450Source23GroupedC07.valid9
#print axioms N11Formalization.C450Source23GroupedC07.valid10
#print axioms N11Formalization.C450Source23GroupedC07.valid11
#print axioms N11Formalization.C450Source23GroupedC07.valid12
#print axioms N11Formalization.C450Source23GroupedC07.valid13
#print axioms N11Formalization.C450Source23GroupedC07.valid14
#print axioms N11Formalization.C450Source23GroupedC07.valid15
#print axioms N11Formalization.C450Source23GroupedC07.valid16
#print axioms N11Formalization.C450Source23GroupedC07.bound
#print axioms N11Formalization.C450Source23GroupedC07.endpoint_checks
