import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((93671339:ℚ)/156250000),((6513484281:ℚ)/10000000000),((913042051:ℚ)/1668750000),((7025484281:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6619237683:ℚ)/10000000000),((-3992942235765255838679289831361:ℚ)/1161753112792968750000000000000000),((-12662062496039603521389:ℚ)/90250000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6470324203:ℚ)/10000000000),((6751122333:ℚ)/10000000000),((8958988261:ℚ)/15800000000),((7263122333:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5522268797:ℚ)/10000000000),((-407351874664542747123759002214080328650484938178379799:ℚ)/73955850000000000000000000000000000000000000000000000000),((-52238938552172924650624781:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((6707984961:ℚ)/10000000000),((3434968929:ℚ)/5000000000),((64851864649:ℚ)/112500000000),((3690968929:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2446845509:ℚ)/5000000000),((-19128537757445191202986386908028767483159601057431796811:ℚ)/2966308593750000000000000000000000000000000000000000000000),((-157292910213336304060246367:ℚ)/1108992000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6826811263:ℚ)/10000000000),((1397750241:ℚ)/2000000000),((65921301367:ℚ)/114400000000),((1500150241:ℚ)/2250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2274958909:ℚ)/5000000000),((-5553306898246649669483451309684661040167313555905265581:ℚ)/850678400000000000000000000000000000000000000000000000000),((-52528102634610378364530421:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((6945635029:ℚ)/10000000000),((1409631419:ℚ)/2000000000),((66990715261:ℚ)/115350000000),((1512031419:ℚ)/2288000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2090040507:ℚ)/5000000000),((-50094805688088556619040449460716218811703291806431515359:ℚ)/7194391665820312500000000000000000000000000000000000000000),((-52625979816295143108374669:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((7005045999:ℚ)/10000000000),((7107562481:ℚ)/10000000000),((67525413991:ℚ)/116300000000),((7619562481:ℚ)/11535000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((497891421:ℚ)/1250000000),((-2750091768192053527853029364640503768667026984422710263:ℚ)/393259436750000000000000000000000000000000000000000000000),((-158025592966672072563995327:ℚ)/1108992000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((9:ℚ)/16),((5:ℚ)/8),((3532228191:ℚ)/5000000000),((7166967373:ℚ)/10000000000),((34030053719:ℚ)/58625000000),((7678967373:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3776499979:ℚ)/10000000000),((-947383998146147831233874284644259837583351870304919267:ℚ)/134924807739257812500000000000000000000000000000000000000),((-39543451253125991374320287:ℚ)/277248000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7123866191:ℚ)/10000000000),((1445274357:ℚ)/2000000000),((68594795719:ℚ)/118200000000),((1547674357:ℚ)/2345000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((711699333:ℚ)/2000000000),((-6062506068831092298324121622836204486404387760909183141:ℚ)/860104462500000000000000000000000000000000000000000000000),((-52774191867465856683817429:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((7183275439:ℚ)/10000000000),((7285775727:ℚ)/10000000000),((69129478951:ℚ)/119150000000),((7797775727:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3326882399:ℚ)/10000000000),((-224365063725330648883691419443083541714789054159230314349:ℚ)/31716365360156250000000000000000000000000000000000000000000),((-52823968250953212921709589:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((7242684141:ℚ)/10000000000),((7345179211:ℚ)/10000000000),((69664157269:ℚ)/120100000000),((7857179211:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3078582143:ℚ)/10000000000),((-4803293746033001215035276485073573201841756693452359237:ℚ)/676688906640625000000000000000000000000000000000000000000),((-158621792485942614303476087:ℚ)/1108992000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((730209231:ℚ)/1000000000),((925572781:ℚ)/1250000000),((7019883079:ℚ)/12105000000),((989572781:ℚ)/1501250000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2809169873:ℚ)/10000000000),((-974604321056487418094319616097643423577933351419887:ℚ)/136864047656250000000000000000000000000000000000000000),((-1587722388191903476434047:ℚ)/11089920000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((7361499957:ℚ)/10000000000),((466499053:ℚ)/625000000),((70733499613:ℚ)/122000000000),((166166351:ℚ)/252187500),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1255928067:ℚ)/5000000000),((-81058937494198459977989033631130483062421225606095900781:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-158923243765543832643675623:ℚ)/1108992000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((927613387:ℚ)/1250000000),((7582788777:ℚ)/10000000000),((8908520483:ℚ)/15487500000),((8094788777:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2175223771:ℚ)/10000000000),((-13208846192883713317309442708421963332816337862198057:ℚ)/1934829629516601562500000000000000000000000000000000000),((-828514621593889845599821:ℚ)/5776000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7539719893:ℚ)/10000000000),((1925397769:ℚ)/2500000000),((1955067001:ℚ)/3400000000),((684465923:ℚ)/1032500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((63016269:ℚ)/500000000),((-1647877913988828624255536749209647142339832412857:ℚ)/239892578125000000000000000000000000000000000000000),((-53126536820881154420684941:ℚ)/369664000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((957316349:ℚ)/1250000000),((793919107:ℚ)/1000000000),((9175847141:ℚ)/16200000000),((845119107:ℚ)/1258000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-6181111616180471927555007018604903619970691871521631:ℚ)/984150000000000000000000000000000000000000000000000000),((-18413563:ℚ)/128000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7896147229:ℚ)/10000000000),((2459954989:ℚ)/2500000000),((75545325061:ℚ)/160000000000),((862651663:ℚ)/1080000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-764461188067876885912950514746853:ℚ)/48000000000000000000000000000000000000),((-18413563:ℚ)/128000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((9796879511:ℚ)/10000000000),((13640558063:ℚ)/10000000000),((92651915599:ℚ)/220800000000),((14152558063:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((61432032596126240449534139:ℚ)/12188160000000000000000000000),((-18413563:ℚ)/128000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC26
#check @N11Formalization.C450NinthGroupedC26.bound
#print axioms N11Formalization.C450NinthGroupedC26.valid0
#print axioms N11Formalization.C450NinthGroupedC26.valid1
#print axioms N11Formalization.C450NinthGroupedC26.valid2
#print axioms N11Formalization.C450NinthGroupedC26.valid3
#print axioms N11Formalization.C450NinthGroupedC26.valid4
#print axioms N11Formalization.C450NinthGroupedC26.valid5
#print axioms N11Formalization.C450NinthGroupedC26.valid6
#print axioms N11Formalization.C450NinthGroupedC26.valid7
#print axioms N11Formalization.C450NinthGroupedC26.valid8
#print axioms N11Formalization.C450NinthGroupedC26.valid9
#print axioms N11Formalization.C450NinthGroupedC26.valid10
#print axioms N11Formalization.C450NinthGroupedC26.valid11
#print axioms N11Formalization.C450NinthGroupedC26.valid12
#print axioms N11Formalization.C450NinthGroupedC26.valid13
#print axioms N11Formalization.C450NinthGroupedC26.valid14
#print axioms N11Formalization.C450NinthGroupedC26.valid15
#print axioms N11Formalization.C450NinthGroupedC26.valid16
#print axioms N11Formalization.C450NinthGroupedC26.bound
#print axioms N11Formalization.C450NinthGroupedC26.endpoint_checks
