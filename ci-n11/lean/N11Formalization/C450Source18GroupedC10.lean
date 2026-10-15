import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((1282309523:ℚ)/2000000000),((838236739:ℚ)/1250000000),((-4587657173:ℚ)/12400000000),((-2758928569:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5667977617:ℚ)/10000000000),((22437278972890761682375610538396835980451079906782567271:ℚ)/317573784375000000000000000000000000000000000000000000000),((448432005550321352825157:ℚ)/3696640000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((51953921:ℚ)/78125000),((273006937:ℚ)/400000000),((-1501448559:ℚ)/4120000000),((-113361763:ℚ)/409765625),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5053328179:ℚ)/10000000000),((1521487150441128059718713367306676980537941420440943:ℚ)/22145924502424895763397216796875000000000000000000000),((330040650382313031189:ℚ)/2820312500000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((33846751:ℚ)/50000000),((868054247:ℚ)/1250000000),((-4796379729:ℚ)/13112500000),((-74340253:ℚ)/267000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2359524439:ℚ)/5000000000),((1069870988692266944005878267585676143349419776043679:ℚ)/15599091396093750000000000000000000000000000000000000),((265401300652977380333:ℚ)/2310400000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6888580673:ℚ)/10000000000),((882959571:ℚ)/1250000000),((-4900716997:ℚ)/13350000000),((-15225742019:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((436132547:ℚ)/1000000000),((9172668016672579279868343807015622914136044589778542276619:ℚ)/133955308320703125000000000000000000000000000000000000000000),((10416859405722479798543357:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7007794251:ℚ)/10000000000),((7123291423:ℚ)/10000000000),((-39623039961:ℚ)/108700000000),((-15583382753:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((79475957:ℚ)/200000000),((3154410580260096678578335112340354825865017475372022209279:ℚ)/46648130220373535156250000000000000000000000000000000000000),((10217192812938697612765333:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7067394981:ℚ)/10000000000),((7182902133:ℚ)/10000000000),((-2355312643:ℚ)/6450000000),((-15762184943:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3766000079:ℚ)/10000000000),((911257315562324713359056663289740118725231816063690459:ℚ)/13483668310546875000000000000000000000000000000000000000),((10117181379147001812292213:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1781747953:ℚ)/2500000000),((1448501761:ℚ)/2000000000),((-8091512327:ℚ)/22120000000),((-3985243859:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1773336497:ℚ)/5000000000),((2825439201652895530795367766656093780619260918845256287:ℚ)/41830773300600051879882812500000000000000000000000000000),((626065686574354055577597:ℚ)/5776000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7186584843:ℚ)/10000000000),((3651055771:ℚ)/5000000000),((-20437390397:ℚ)/55775000000),((-16119754529:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((258869:ℚ)/781250),((981642704052660618482722875808720588490519473558998623351:ℚ)/14541140198707580566406250000000000000000000000000000000000),((9916801489052646598756117:ℚ)/92416000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1811543543:ℚ)/2500000000),((7361710443:ℚ)/10000000000),((-41291973101:ℚ)/112500000000),((-4074630629:ℚ)/14181250000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((765847791:ℚ)/2500000000),((13530176659588449117431966565150058828408584071188007:ℚ)/200528488122940063476562500000000000000000000000000000),((1699520905396797309797:ℚ)/16000000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((1826439973:ℚ)/2500000000),((1855326401:ℚ)/2500000000),((-10427284807:ℚ)/28362500000),((-28806433:ℚ)/100000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1395855193:ℚ)/5000000000),((478180122101000135260304805915229641099737365987519:ℚ)/7090625000000000000000000000000000000000000000000000),((607246539574626995540757:ℚ)/5776000000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1473068419:ℚ)/2000000000),((7540485079:ℚ)/10000000000),((-42543395553:ℚ)/114400000000),((-3331205257:ℚ)/11630000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2491435323:ℚ)/10000000000),((47870748104577949664684382619605063605496211027457207133:ℚ)/702951243190625000000000000000000000000000000000000000000),((384613480290825270035813:ℚ)/3696640000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((1871124073:ℚ)/2500000000),((7659650673:ℚ)/10000000000),((-43377554711:ℚ)/116300000000),((-4253372219:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1745652253:ℚ)/10000000000),((7382787881907159533005044361454424011009804210420677273:ℚ)/108539658190917968750000000000000000000000000000000000000),((588360171022032370984557:ℚ)/5776000000000000000000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((7603637431:ℚ)/10000000000),((1579588567:ℚ)/2000000000),((-9009119969:ℚ)/23640000000),((-17370912293:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((9675174407752113664985448187300770370945126781938320076147:ℚ)/139735178125000000000000000000000000000000000000000000000000),((6383577:ℚ)/64000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((1960470747:ℚ)/2500000000),((4187193583:ℚ)/5000000000),((-24190355081:ℚ)/61000000000),((-4521412241:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((19295796252887162279253735536938121331398487383514561901:ℚ)/270149175000000000000000000000000000000000000000000000000),((6383577:ℚ)/64000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((8318242381:ℚ)/10000000000),((321212119:ℚ)/312500000),((-1928484833:ℚ)/4050000000),((-19514727143:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((10697075245760686714290413997285667064254193419949583917101:ℚ)/129600000000000000000000000000000000000000000000000000000000),((6383577:ℚ)/64000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((5111192241:ℚ)/5000000000),((1760493309:ℚ)/1250000000),((-11043453163:ℚ)/20000000000),((-12613576723:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((37404593560097440164454345643680287087267913798753004243:ℚ)/394210800000000000000000000000000000000000000000000000000),((6383577:ℚ)/64000000)⟩
theorem valid15 : Valid source18 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC10
#check @N11Formalization.C450Source18GroupedC10.bound
#print axioms N11Formalization.C450Source18GroupedC10.valid0
#print axioms N11Formalization.C450Source18GroupedC10.valid1
#print axioms N11Formalization.C450Source18GroupedC10.valid2
#print axioms N11Formalization.C450Source18GroupedC10.valid3
#print axioms N11Formalization.C450Source18GroupedC10.valid4
#print axioms N11Formalization.C450Source18GroupedC10.valid5
#print axioms N11Formalization.C450Source18GroupedC10.valid6
#print axioms N11Formalization.C450Source18GroupedC10.valid7
#print axioms N11Formalization.C450Source18GroupedC10.valid8
#print axioms N11Formalization.C450Source18GroupedC10.valid9
#print axioms N11Formalization.C450Source18GroupedC10.valid10
#print axioms N11Formalization.C450Source18GroupedC10.valid11
#print axioms N11Formalization.C450Source18GroupedC10.valid12
#print axioms N11Formalization.C450Source18GroupedC10.valid13
#print axioms N11Formalization.C450Source18GroupedC10.valid14
#print axioms N11Formalization.C450Source18GroupedC10.valid15
#print axioms N11Formalization.C450Source18GroupedC10.bound
#print axioms N11Formalization.C450Source18GroupedC10.endpoint_checks
