import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((155719327:ℚ)/250000000),((3363797573:ℚ)/5000000000),((-7851392719:ℚ)/49600000000),((-30573109:ℚ)/445000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((762658427:ℚ)/1250000000),((92342396056827391029162396081930763114806959801643:ℚ)/4268366992187500000000000000000000000000000000000000),((45013301305289439752883943:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6704216593:ℚ)/10000000000),((3423237359:ℚ)/5000000000),((-8029712077:ℚ)/53400000000),((-4144216593:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2452114393:ℚ)/5000000000),((1856382316338833015848607516760011319550459707502957192361:ℚ)/89303538880468750000000000000000000000000000000000000000000),((35982268547165135970156127:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((852883471:ℚ)/1250000000),((6965349831:ℚ)/10000000000),((-16416049493:ℚ)/108700000000),((-532883471:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4561113557:ℚ)/10000000000),((2178653715492242034746072975146772919541365503915641243:ℚ)/105185596732521057128906250000000000000000000000000000000),((135680476003077096080660687:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((6941915463:ℚ)/10000000000),((3512392893:ℚ)/5000000000),((-8297178679:ℚ)/55300000000),((-4381915463:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4192121051:ℚ)/10000000000),((771013078051040370904169937372703349941518538994622299183:ℚ)/37480372877337646484375000000000000000000000000000000000000),((31730168488097426946196983:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((7001338061:ℚ)/10000000000),((7084220711:ℚ)/10000000000),((-16772662133:ℚ)/111550000000),((-4441338061:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((399569143:ℚ)/1000000000),((597334421171346496918272706100580956873081129856701234161:ℚ)/29082280397415161132812500000000000000000000000000000000000),((122807733759636137968453007:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((3530379927:ℚ)/5000000000),((7143654631:ℚ)/10000000000),((-16950963893:ℚ)/112500000000),((-2250379927:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((473708587:ℚ)/1250000000),((21934198485983622843652091771548802729878429790749837:ℚ)/1069485269989013671875000000000000000000000000000000000),((118699306600252730121199887:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((7120180863:ℚ)/10000000000),((720308757:ℚ)/1000000000),((-1712926271:ℚ)/11345000000),((-4560180863:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3572389469:ℚ)/10000000000),((54354239618194809732799724294561739711017222451162952521051:ℚ)/2654010273200000000000000000000000000000000000000000000000000),((1145953908256990723722183:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((3589800553:ℚ)/5000000000),((3631259777:ℚ)/5000000000),((-8653779331:ℚ)/57200000000),((-2309800553:ℚ)/28837500000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3341654471:ℚ)/10000000000),((51370076244742722648866188357274285133358714172642309:ℚ)/2511713887237071990966796875000000000000000000000000000),((27623996261835612319983743:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7239020603:ℚ)/10000000000),((3660975303:ℚ)/5000000000),((-8742925909:ℚ)/57675000000),((-4679020603:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1547225327:ℚ)/5000000000),((19303209294893178399076549971368883296665577020701969454939:ℚ)/945051583939843750000000000000000000000000000000000000000000),((26600271925095917663761103:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-3:ℚ)/16),((-1:ℚ)/8),((7298439373:ℚ)/10000000000),((1845345187:ℚ)/2500000000),((-4416035561:ℚ)/29075000000),((-4738439373:ℚ)/58625000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2826455257:ℚ)/10000000000),((29877235820645072921102305025153628137915233478740939105263:ℚ)/1464563813073730468750000000000000000000000000000000000000000),((6394418580983325234288823:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((7357857433:ℚ)/10000000000),((3720405001:ℚ)/5000000000),((-8921215003:ℚ)/58625000000),((-1599285811:ℚ)/19700000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1265533529:ℚ)/5000000000),((114157735486995222674385364970749274945951038454383629463:ℚ)/5602624901562500000000000000000000000000000000000000000000),((24556203126787666900901167:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7417274799:ℚ)/10000000000),((7559665933:ℚ)/10000000000),((-18198997799:ℚ)/118200000000),((-4857274799:ℚ)/60050000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((17578079:ℚ)/80000000),((4082928317829126224043751595934772781447687787571471901993:ℚ)/199961571912304687500000000000000000000000000000000000000000),((94708309587134411515560663:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((1471896:ℚ)/1953125),((7678518559:ℚ)/10000000000),((-18555555677:ℚ)/120100000000),((-1943792:ℚ)/23828125),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1297590931:ℚ)/10000000000),((1551772945829604745063552714543472635865397623617:ℚ)/76164728309959173202514648437500000000000000000000),((1764201868479:ℚ)/304000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7654937661:ℚ)/10000000000),((8153898939:ℚ)/10000000000),((-19981696817:ℚ)/122000000000),((-5094937661:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((715854361323027138527219864476703968410194999489905832299:ℚ)/34579094400000000000000000000000000000000000000000000000000),((5596909:ℚ)/1024000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((8130234707:ℚ)/10000000000),((5027529391:ℚ)/5000000000),((-12842588173:ℚ)/64800000000),((-5570234707:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1883829196470426734690715631416727505987606904185319571697:ℚ)/86400000000000000000000000000000000000000000000000000000000),((5596909:ℚ)/1024000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((10031140503:ℚ)/10000000000),((3464104957:ℚ)/2500000000),((-9272314871:ℚ)/40000000000),((-7471140503:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((151803347640490510968210067971875985855400083962692346197:ℚ)/6307372800000000000000000000000000000000000000000000000000),((5596909:ℚ)/1024000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC14
#check @N11Formalization.C450NinthGroupedC14.bound
#print axioms N11Formalization.C450NinthGroupedC14.valid0
#print axioms N11Formalization.C450NinthGroupedC14.valid1
#print axioms N11Formalization.C450NinthGroupedC14.valid2
#print axioms N11Formalization.C450NinthGroupedC14.valid3
#print axioms N11Formalization.C450NinthGroupedC14.valid4
#print axioms N11Formalization.C450NinthGroupedC14.valid5
#print axioms N11Formalization.C450NinthGroupedC14.valid6
#print axioms N11Formalization.C450NinthGroupedC14.valid7
#print axioms N11Formalization.C450NinthGroupedC14.valid8
#print axioms N11Formalization.C450NinthGroupedC14.valid9
#print axioms N11Formalization.C450NinthGroupedC14.valid10
#print axioms N11Formalization.C450NinthGroupedC14.valid11
#print axioms N11Formalization.C450NinthGroupedC14.valid12
#print axioms N11Formalization.C450NinthGroupedC14.valid13
#print axioms N11Formalization.C450NinthGroupedC14.valid14
#print axioms N11Formalization.C450NinthGroupedC14.valid15
#print axioms N11Formalization.C450NinthGroupedC14.bound
#print axioms N11Formalization.C450NinthGroupedC14.endpoint_checks
