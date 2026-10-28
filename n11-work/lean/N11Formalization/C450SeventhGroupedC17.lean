import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((3090185627:ℚ)/5000000000),((266880123:ℚ)/400000000),((8:ℚ)/267),((420480123:ℚ)/3968000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6211551281:ℚ)/10000000000),((5343123897699957670516915836246941551:ℚ)/556733719904256000000000000000000000000),((-8797631782458293:ℚ)/486400000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((332785043:ℚ)/500000000),((3395402741:ℚ)/5000000000),((32:ℚ)/1087),((5315402741:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((314880567:ℚ)/625000000),((15617456626804964535284869019571879919449937588262803465211497:ℚ)/1686763270631025000000000000000000000000000000000000000000000000),((-947425373234237:ℚ)/48640000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6774526053:ℚ)/10000000000),((863700761:ℚ)/1250000000),((16:ℚ)/553),((1343700761:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4704045351:ℚ)/10000000000),((4136133409326518955573060934839916112350225749195918558013:ℚ)/449490200165092849731445312500000000000000000000000000000000),((-19286797917322827:ℚ)/972800000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((6893348661:ℚ)/10000000000),((6969005743:ℚ)/10000000000),((64:ℚ)/2231),((10809005743:ℚ)/110600000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4346450601:ℚ)/10000000000),((27479552137627034487356823975919052430381676122352079455488159:ℚ)/3006190535346775000000000000000000000000000000000000000000000000),((-19625081010571899:ℚ)/972800000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((1738189759:ℚ)/2500000000),((3514202491:ℚ)/5000000000),((32:ℚ)/1125),((5434202491:ℚ)/55775000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4156929381:ℚ)/10000000000),((17408137535023345626207600153612437885336058470248393307:ℚ)/1909527606298828125000000000000000000000000000000000000000),((-4948554978092881:ℚ)/243200000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((7012168813:ℚ)/10000000000),((1417560763:ℚ)/2000000000),((64:ℚ)/2269),((2185560763:ℚ)/22500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((791779629:ℚ)/2000000000),((1666371686277795911468356528731273965511147966855277207691533:ℚ)/183259529736328125000000000000000000000000000000000000000000000),((-19963357111689667:ℚ)/972800000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((7071578007:ℚ)/10000000000),((1786800563:ℚ)/2500000000),((4:ℚ)/143),((2746800563:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3751005451:ℚ)/10000000000),((48089681862346352783945679282774630671896209707042088887:ℚ)/5301794978425537109375000000000000000000000000000000000000),((-20132492651230713:ℚ)/972800000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((7130986633:ℚ)/10000000000),((7206600303:ℚ)/10000000000),((64:ℚ)/2307),((11046600303:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3531506109:ℚ)/10000000000),((18777528306783552804836202296082303201052833965348011027396531:ℚ)/2075114370872400000000000000000000000000000000000000000000000000),((-20301626573699047:ℚ)/972800000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((1438078941:ℚ)/2000000000),((7265997977:ℚ)/10000000000),((32:ℚ)/1163),((11105997977:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1649039629:ℚ)/5000000000),((780921865110017498406569992538892115381525243018531318873189:ℚ)/86496987920417015625000000000000000000000000000000000000000000),((-4094151783790419:ℚ)/194560000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),(0:ℚ),((1:ℚ)/16),((1812450559:ℚ)/2500000000),((7325395283:ℚ)/10000000000),((64:ℚ)/2345),((11165395283:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3047521639:ℚ)/10000000000),((7305581613900937171974362928423872005075506981858254281019959:ℚ)/810953802815313281250000000000000000000000000000000000000000000),((-5159972431000081:ℚ)/243200000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7309209239:ℚ)/10000000000),((738479223:ℚ)/1000000000),((16:ℚ)/591),((1122479223:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2775192207:ℚ)/10000000000),((3954169493070065088579390829186607368248545956941868824433:ℚ)/439848936538439941406250000000000000000000000000000000000000),((-20809019025854201:ℚ)/972800000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((460538483:ℚ)/625000000),((7503585083:ℚ)/10000000000),((32:ℚ)/1201),((11343585083:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2473905887:ℚ)/10000000000),((200516818208558386303119043254291715020238062049190051574884191:ℚ)/22331079662660325000000000000000000000000000000000000000000000000),((-1311134179023197:ℚ)/60800000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((7487427209:ℚ)/10000000000),((38111883:ℚ)/50000000),((8:ℚ)/305),((57311883:ℚ)/600500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((53853319:ℚ)/312500000),((22524968058017358072656183111973970426069489219632797:ℚ)/2517959421609765625000000000000000000000000000000000000),((-21316398279507431:ℚ)/972800000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((3803118387:ℚ)/5000000000),((809753049:ℚ)/1000000000),((2:ℚ)/81),((1193753049:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((83359828598762150603673335619526615819548203252121002759:ℚ)/9307639631250000000000000000000000000000000000000000000000),((-2846959:ℚ)/128000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((2020364389:ℚ)/2500000000),((4998999901:ℚ)/5000000000),((1:ℚ)/50),((6918999901:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1433980523033087011795128540398077951322463230809835657:ℚ)/159432300000000000000000000000000000000000000000000000000),((-2846959:ℚ)/128000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((2495532709:ℚ)/2500000000),((13798550651:ℚ)/10000000000),((1:ℚ)/69),((17638550651:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((24107698814785716863622224823976701165647:ℚ)/2437632000000000000000000000000000000000000),((-2846959:ℚ)/128000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC17
#check @N11Formalization.C450SeventhGroupedC17.bound
#print axioms N11Formalization.C450SeventhGroupedC17.valid0
#print axioms N11Formalization.C450SeventhGroupedC17.valid1
#print axioms N11Formalization.C450SeventhGroupedC17.valid2
#print axioms N11Formalization.C450SeventhGroupedC17.valid3
#print axioms N11Formalization.C450SeventhGroupedC17.valid4
#print axioms N11Formalization.C450SeventhGroupedC17.valid5
#print axioms N11Formalization.C450SeventhGroupedC17.valid6
#print axioms N11Formalization.C450SeventhGroupedC17.valid7
#print axioms N11Formalization.C450SeventhGroupedC17.valid8
#print axioms N11Formalization.C450SeventhGroupedC17.valid9
#print axioms N11Formalization.C450SeventhGroupedC17.valid10
#print axioms N11Formalization.C450SeventhGroupedC17.valid11
#print axioms N11Formalization.C450SeventhGroupedC17.valid12
#print axioms N11Formalization.C450SeventhGroupedC17.valid13
#print axioms N11Formalization.C450SeventhGroupedC17.valid14
#print axioms N11Formalization.C450SeventhGroupedC17.valid15
#print axioms N11Formalization.C450SeventhGroupedC17.bound
#print axioms N11Formalization.C450SeventhGroupedC17.endpoint_checks
