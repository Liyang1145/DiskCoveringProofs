import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((6211768727:ℚ)/10000000000),((1677609243:ℚ)/2500000000),((-1037609243:ℚ)/12400000000),((-451768727:ℚ)/106800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1228041679:ℚ)/2000000000),((1295238267237727723740248169579272309988076041855684068123:ℚ)/59005905300000000000000000000000000000000000000000000000000),((-816267988203723201693141:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((668735517:ℚ)/1000000000),((6829354361:ℚ)/10000000000),((-4269354361:ℚ)/53400000000),((-92735517:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2475563651:ℚ)/5000000000),((512148617458103603145861051804288808632844562604066389:ℚ)/24081853181250000000000000000000000000000000000000000000),((-18790652266950240635010189:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((3403119473:ℚ)/5000000000),((6948265987:ℚ)/10000000000),((-4388265987:ℚ)/54350000000),((-523119473:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1152782907:ℚ)/2500000000),((162947509709134024611057974638051829425487318923409979329:ℚ)/7693575075292968750000000000000000000000000000000000000000),((-20185159767398372425769221:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((6925118117:ℚ)/10000000000),((7007719731:ℚ)/10000000000),((-635388533:ℚ)/7900000000),((-1165118117:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2123046561:ℚ)/5000000000),((902106248435860265921544543033495742573007516534493462593:ℚ)/42834711859814453125000000000000000000000000000000000000000),((-21604427543857391750928549:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((6984556051:ℚ)/10000000000),((3533586071:ℚ)/5000000000),((-2253586071:ℚ)/27887500000),((-1224556051:ℚ)/112500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((405207717:ℚ)/1000000000),((4891150806791838711904734703560816354947661017498702021333:ℚ)/232658243179321289062500000000000000000000000000000000000000),((-5575273065542292023794669:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((7043992919:ℚ)/10000000000),((1425324651:ℚ)/2000000000),((-913324651:ℚ)/11250000000),((-1283992919:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3848861783:ℚ)/10000000000),((4309549363899780405082316289588674415071897674104727229:ℚ)/205341171837890625000000000000000000000000000000000000000),((-919901105323357238155509:ℚ)/73932800000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((5682743:ℚ)/8000000),((7186073101:ℚ)/10000000000),((-4626073101:ℚ)/56725000000),((-1074743:ℚ)/91520000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((726980067:ℚ)/2000000000),((227778775383221068364404259229947063791094150052433:ℚ)/10870826079027200000000000000000000000000000000000000),((-23693734009573502526435109:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((7162863569:ℚ)/10000000000),((452845107:ℚ)/625000000),((-292845107:ℚ)/3575000000),((-1402863569:ℚ)/115350000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1704082659:ℚ)/5000000000),((305727113537076833576488787548058388075565649141856989:ℚ)/14613608071197509765625000000000000000000000000000000000),((-5014332174157143514539:ℚ)/380000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7222297401:ℚ)/10000000000),((3652484559:ℚ)/5000000000),((-2372484559:ℚ)/28837500000),((-1462297401:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3165908979:ℚ)/10000000000),((473804550784679375943649217272492730674369062953273492150753:ℚ)/22681238014556250000000000000000000000000000000000000000000000),((-6271365248389086169253629:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/8),((-1:ℚ)/16),((7281730271:ℚ)/10000000000),((7364415349:ℚ)/10000000000),((-4804415349:ℚ)/58150000000),((-1521730271:ℚ)/117250000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1452122473:ℚ)/5000000000),((104746472635146547614942440049353830711174289337220645224763:ℚ)/5021361644824218750000000000000000000000000000000000000000000),((-25780982208395229572835509:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7341162201:ℚ)/10000000000),((7423860433:ℚ)/10000000000),((-4863860433:ℚ)/58625000000),((-527054067:ℚ)/39400000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2617353643:ℚ)/10000000000),((133387644577884614809639157757324447571050570027975717451:ℚ)/6402999887500000000000000000000000000000000000000000000000),((-26476275607085120278615101:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((115634269:ℚ)/156250000),((1885686817:ℚ)/2500000000),((-415228939:ℚ)/4925000000),((-25634269:ℚ)/1876562500),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2295790969:ℚ)/10000000000),((127188092474097486889479329908267625931360745173038309:ℚ)/6102342892831563949584960937500000000000000000000000000),((-1696495534290618009611101:ℚ)/115520000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((3759726291:ℚ)/5000000000),((1532325967:ℚ)/2000000000),((-1020325967:ℚ)/12010000000),((-879726291:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1457197201:ℚ)/10000000000),((35425785309945987102365149693466142835549721269363481387561:ℚ)/1703776131250000000000000000000000000000000000000000000000000),((-1879066649328243:ℚ)/121600000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((7638308537:ℚ)/10000000000),((8137121171:ℚ)/10000000000),((-5577121171:ℚ)/61000000000),((-1878308537:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5798972135997496342314939969581809378334794554023324519741:ℚ)/276632755200000000000000000000000000000000000000000000000000),((-409151:ℚ)/25600000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((2028425313:ℚ)/2500000000),((10038619217:ℚ)/10000000000),((-7478619217:ℚ)/64800000000),((-588425313:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((700199977771299417240678658318044061997474167007161395427:ℚ)/32400000000000000000000000000000000000000000000000000000000),((-409151:ℚ)/25600000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((1251862337:ℚ)/1250000000),((6920188473:ℚ)/5000000000),((-5640188473:ℚ)/40000000000),((-531862337:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2335198641493016880563418321917152677391412762812760369:ℚ)/98552700000000000000000000000000000000000000000000000000),((-409151:ℚ)/25600000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC15
#check @N11Formalization.C450TenthGroupedC15.bound
#print axioms N11Formalization.C450TenthGroupedC15.valid0
#print axioms N11Formalization.C450TenthGroupedC15.valid1
#print axioms N11Formalization.C450TenthGroupedC15.valid2
#print axioms N11Formalization.C450TenthGroupedC15.valid3
#print axioms N11Formalization.C450TenthGroupedC15.valid4
#print axioms N11Formalization.C450TenthGroupedC15.valid5
#print axioms N11Formalization.C450TenthGroupedC15.valid6
#print axioms N11Formalization.C450TenthGroupedC15.valid7
#print axioms N11Formalization.C450TenthGroupedC15.valid8
#print axioms N11Formalization.C450TenthGroupedC15.valid9
#print axioms N11Formalization.C450TenthGroupedC15.valid10
#print axioms N11Formalization.C450TenthGroupedC15.valid11
#print axioms N11Formalization.C450TenthGroupedC15.valid12
#print axioms N11Formalization.C450TenthGroupedC15.valid13
#print axioms N11Formalization.C450TenthGroupedC15.valid14
#print axioms N11Formalization.C450TenthGroupedC15.valid15
#print axioms N11Formalization.C450TenthGroupedC15.bound
#print axioms N11Formalization.C450TenthGroupedC15.endpoint_checks
