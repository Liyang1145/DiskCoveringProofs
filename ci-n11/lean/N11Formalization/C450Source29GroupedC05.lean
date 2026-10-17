import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((861586953:ℚ)/1250000000),((7115173431:ℚ)/10000000000),((-17025520293:ℚ)/24800000000),((-7237456483:ℚ)/12637500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4348490719:ℚ)/10000000000),((5324387532172247042282523182680710851:ℚ)/15641745244628906250000000000000000000),((1957688895355204511371479:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7012388977:ℚ)/10000000000),((717495687:ℚ)/1000000000),((-573495687:ℚ)/842500000),((-59216278747:ℚ)/102050000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((1979073433:ℚ)/5000000000),((299432611381992986860164534550885023129413343873502175307:ℚ)/891105881884765625000000000000000000000000000000000000000),((124820274481285619023203399:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((7072222327:ℚ)/10000000000),((3617366349:ℚ)/5000000000),((-8692099047:ℚ)/12756250000),((-59874445597:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((23429317:ℚ)/62500000),((561758419596989326307310525057532358631336776335919963756659:ℚ)/1672691855250000000000000000000000000000000000000000000000000),((124620379263113624614643799:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((57056377:ℚ)/80000000),((290584713:ℚ)/400000000),((-698954139:ℚ)/1030000000),((-484260147:ℚ)/827800000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((1763734657:ℚ)/5000000000),((476057782765653989571157797816540542190905552460049:ℚ)/1426440112257226562500000000000000000000000000000000),((7960232954845414170999:ℚ)/14786560000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7161956393:ℚ)/10000000000),((7294501127:ℚ)/10000000000),((-17563503381:ℚ)/25868750000),((-6762391147:ℚ)/11550000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((3411734587:ℚ)/10000000000),((531974491807012225440230673427669580538880037191324003597:ℚ)/1594341635906250000000000000000000000000000000000000000000),((124276647959663469222064919:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7191863611:ℚ)/10000000000),((7324382631:ℚ)/10000000000),((-1961460877:ℚ)/2887500000),((-61190499721:ℚ)/104425000000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3292106149:ℚ)/10000000000),((548429761089278622015436778529011740823172810836213661611819:ℚ)/1644013763361621093750000000000000000000000000000000000000000),((124174071236011029869487951:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((902721101:ℚ)/1250000000),((183856559:ℚ)/250000000),((-443569677:ℚ)/652656250),((-7689932111:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1584071123:ℚ)/5000000000),((19630235206649971382051789931913401537359870069069092567123:ℚ)/58857389537023925781250000000000000000000000000000000000000),((1938607965031672031687231:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1812918003:ℚ)/2500000000),((3707008297:ℚ)/5000000000),((-8961024891:ℚ)/13112500000),((-15462098033:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3039311703:ℚ)/10000000000),((40742344085677605075790247070145042487349436991279830877093:ℚ)/121492122290490722656250000000000000000000000000000000000000),((407916642107413373461541:ℚ)/760000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((146229451:ℚ)/200000000),((7473764017:ℚ)/10000000000),((-18101292051:ℚ)/26462500000),((-416707987:ℚ)/712000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((138215073:ℚ)/500000000),((1200634632528805789977840609370932498985502406986111417:ℚ)/3581806495200000000000000000000000000000000000000000000),((49518963279007574792431:ℚ)/92416000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7371265437:ℚ)/10000000000),((1898309789:ℚ)/2500000000),((-1538309789:ℚ)/2225000000),((-63163919807:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((614906951:ℚ)/2500000000),((726075403944285486446766373827335638703606396451038384951449:ℚ)/2143284933131250000000000000000000000000000000000000000000000),((123664785878250755314091039:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7490829073:ℚ)/10000000000),((192817229:ℚ)/250000000),((-470451687:ℚ)/679375000),((-9211302829:ℚ)/15800000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((10606277:ℚ)/62500000),((1700516612940456055184671681480862184255631500057150504109:ℚ)/5024375559375000000000000000000000000000000000000000000000),((123085602861627652945320199:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((1902591119:ℚ)/2500000000),((1987879707:ℚ)/2500000000),((-4883639121:ℚ)/6912500000),((-16448502309:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((27914514443440053255627873232606319963249509759813202817937:ℚ)/80854323550000000000000000000000000000000000000000000000000),((8486173:ℚ)/16000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((3924678141:ℚ)/5000000000),((8906052321:ℚ)/10000000000),((-1722935151:ℚ)/2200000000),((-34211459551:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5384951707971950688070067615942487004952918847653586416987:ℚ)/14030042400000000000000000000000000000000000000000000000000),((8486173:ℚ)/16000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8804441839:ℚ)/10000000000),((10812522251:ℚ)/10000000000),((-9372522251:ℚ)/10800000000),((-78928860229:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((364364401642852380412148341139211397363:ℚ)/864000000000000000000000000000000000000),((8486173:ℚ)/16000000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((10711697871:ℚ)/10000000000),((14620101599:ℚ)/10000000000),((-39540304797:ℚ)/40000000000),((-99908676581:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((11814398814596655473239323619:ℚ)/24376320000000000000000000000),((8486173:ℚ)/16000000)⟩
theorem valid14 : Valid source29 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC05
#check @N11Formalization.C450Source29GroupedC05.bound
#print axioms N11Formalization.C450Source29GroupedC05.valid0
#print axioms N11Formalization.C450Source29GroupedC05.valid1
#print axioms N11Formalization.C450Source29GroupedC05.valid2
#print axioms N11Formalization.C450Source29GroupedC05.valid3
#print axioms N11Formalization.C450Source29GroupedC05.valid4
#print axioms N11Formalization.C450Source29GroupedC05.valid5
#print axioms N11Formalization.C450Source29GroupedC05.valid6
#print axioms N11Formalization.C450Source29GroupedC05.valid7
#print axioms N11Formalization.C450Source29GroupedC05.valid8
#print axioms N11Formalization.C450Source29GroupedC05.valid9
#print axioms N11Formalization.C450Source29GroupedC05.valid10
#print axioms N11Formalization.C450Source29GroupedC05.valid11
#print axioms N11Formalization.C450Source29GroupedC05.valid12
#print axioms N11Formalization.C450Source29GroupedC05.valid13
#print axioms N11Formalization.C450Source29GroupedC05.valid14
#print axioms N11Formalization.C450Source29GroupedC05.bound
#print axioms N11Formalization.C450Source29GroupedC05.endpoint_checks
