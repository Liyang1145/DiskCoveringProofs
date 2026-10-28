import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/8),((11:ℚ)/16),((1312481647:ℚ)/2500000000),((698663647:ℚ)/1250000000),((1808481647:ℚ)/2575000000),((10245300117:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8082293451:ℚ)/10000000000),((-42415249078902213745221098535317196762576820079527696267:ℚ)/122738920000000000000000000000000000000000000000000000000),((-2736978760378346535128327:ℚ)/5776000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((2745019867:ℚ)/5000000000),((582944169:ℚ)/1000000000),((1245673289:ℚ)/1780000000),((8460385859:ℚ)/10300000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7635675393:ℚ)/10000000000),((-5255719709674521510903203431953061090290865219113300483:ℚ)/15195734843750000000000000000000000000000000000000000000),((-1727068893935534204290183:ℚ)/3696640000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((5729964067:ℚ)/10000000000),((1487359457:ℚ)/2500000000),((7713964067:ℚ)/10870000000),((7160318009:ℚ)/8900000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7167532193:ℚ)/10000000000),((-170888327436706533379262008030646548815467441721749041439:ℚ)/478938314375000000000000000000000000000000000000000000000),((-10721106376810986819951047:ℚ)/23104000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((5849861739:ℚ)/10000000000),((3034695249:ℚ)/5000000000),((7833861739:ℚ)/11060000000),((43621647739:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1384792031:ℚ)/2000000000),((-132489990330173604280166748460513995504103863580368746551:ℚ)/371575469007568359375000000000000000000000000000000000000),((-42559755537874882085544503:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((2984859713:ℚ)/5000000000),((3094650973:ℚ)/5000000000),((3976859713:ℚ)/5625000000),((44281160703:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3336549049:ℚ)/5000000000),((-189146867217881113701676948010405708658312333033139217:ℚ)/530835446777343750000000000000000000000000000000000000),((-2222537460081241674858773:ℚ)/4864000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((608953919:ℚ)/1000000000),((781155359:ℚ)/1250000000),((807353919:ℚ)/1134500000),((11152708949:ℚ)/14062500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6414062543:ℚ)/10000000000),((-3559899747788308606771231443373601277825844502917761097:ℚ)/9859210252761840820312500000000000000000000000000000000),((-2629537065907582537240143:ℚ)/5776000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((3074717729:ℚ)/5000000000),((3154587133:ℚ)/5000000000),((4066717729:ℚ)/5720000000),((44940458463:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3140578111:ℚ)/5000000000),((-5887251231894376017133140337747524022665690610820560806353:ℚ)/16313215318232421875000000000000000000000000000000000000000),((-41902523941512207479615567:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((1241864591:ℚ)/2000000000),((6369096369:ℚ)/10000000000),((1638664591:ℚ)/2307000000),((90540060059:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6145791663:ℚ)/10000000000),((-30417222305214609111922414415411774102128930584897988081:ℚ)/84326819362500000000000000000000000000000000000000000000),((-166922948044153314214540983:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6269201903:ℚ)/10000000000),((6429009411:ℚ)/10000000000),((8253201903:ℚ)/11630000000),((91199103521:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((375487451:ℚ)/625000000),((-134069367583382008542911144464250229179958161054046891399257:ℚ)/371870111437734375000000000000000000000000000000000000000000),((-166228929613262799115949263:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((1265814503:ℚ)/2000000000),((3244456809:ℚ)/5000000000),((1662614503:ℚ)/2345000000),((45929024899:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5866989947:ℚ)/10000000000),((-8901265139234688088855292219208666174871842803215926796003:ℚ)/24701608370859375000000000000000000000000000000000000000000),((-41382010242359511474095943:ℚ)/92416000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1597233749:ℚ)/2500000000),((3274404603:ℚ)/5000000000),((697744583:ℚ)/985000000),((46258450633:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5723152413:ℚ)/10000000000),((-45588715336052553222722471358952275611150562391344018613:ℚ)/126572319641113281250000000000000000000000000000000000000),((-41205070655874963180619327:ℚ)/92416000000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3224394773:ℚ)/5000000000),((6668575357:ℚ)/10000000000),((4216394773:ℚ)/6005000000),((93834328927:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((557604869:ℚ)/1000000000),((-330396639328122127288581035048959127402140911259836845357677:ℚ)/929686913516250000000000000000000000000000000000000000000000),((-163333286397697370721328847:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((3284237809:ℚ)/5000000000),((6788309463:ℚ)/10000000000),((4276237809:ℚ)/6100000000),((95151404093:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2635464013:ℚ)/5000000000),((-70371144798164051601447077617469585533554163957079036649803:ℚ)/198134511864375000000000000000000000000000000000000000000000),((-161869702023800237625561607:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3344066099:ℚ)/5000000000),((87846093:ℚ)/125000000),((4336066099:ℚ)/6290000000),((1222307023:ℚ)/1525000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2474487517:ℚ)/5000000000),((-362016109779867342237292293977063324962756079665520873:ℚ)/1045686394042968750000000000000000000000000000000000000),((-24806005668204424309197:ℚ)/57760000000000000000000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((1731840577:ℚ)/2500000000),((908369257:ℚ)/1250000000),((2227840577:ℚ)/3240000000),((12552061827:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4238919627:ℚ)/10000000000),((-1841891246852336196999418793571510816831160839616583207:ℚ)/5320289619140625000000000000000000000000000000000000000),((-2431860132268349083842647:ℚ)/5776000000000000000000000)⟩
theorem valid14 : Valid source33 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source33 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((1433297983:ℚ)/2000000000),((1835608199:ℚ)/2000000000),((1830097983:ℚ)/3200000000),((24287690189:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3393861491:ℚ)/10000000000),((-474747311104433336218443681261160536621323767389121631:ℚ)/2040733440000000000000000000000000000000000000000000000),((-15898112377912353:ℚ)/38912000000000000)⟩
theorem valid15 : Valid source33 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((226917657:ℚ)/250000000),((12991009773:ℚ)/10000000000),((276517657:ℚ)/552000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-20552542963511:ℚ)/138000000000000),((-2621201:ℚ)/6400000)⟩
theorem valid16 : Valid source33 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source33 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source33 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source33 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source33 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source33 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source33 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC27
#check @N11Formalization.C450Source33GroupedC27.bound
#print axioms N11Formalization.C450Source33GroupedC27.valid0
#print axioms N11Formalization.C450Source33GroupedC27.valid1
#print axioms N11Formalization.C450Source33GroupedC27.valid2
#print axioms N11Formalization.C450Source33GroupedC27.valid3
#print axioms N11Formalization.C450Source33GroupedC27.valid4
#print axioms N11Formalization.C450Source33GroupedC27.valid5
#print axioms N11Formalization.C450Source33GroupedC27.valid6
#print axioms N11Formalization.C450Source33GroupedC27.valid7
#print axioms N11Formalization.C450Source33GroupedC27.valid8
#print axioms N11Formalization.C450Source33GroupedC27.valid9
#print axioms N11Formalization.C450Source33GroupedC27.valid10
#print axioms N11Formalization.C450Source33GroupedC27.valid11
#print axioms N11Formalization.C450Source33GroupedC27.valid12
#print axioms N11Formalization.C450Source33GroupedC27.valid13
#print axioms N11Formalization.C450Source33GroupedC27.valid14
#print axioms N11Formalization.C450Source33GroupedC27.valid15
#print axioms N11Formalization.C450Source33GroupedC27.valid16
#print axioms N11Formalization.C450Source33GroupedC27.bound
#print axioms N11Formalization.C450Source33GroupedC27.endpoint_checks
