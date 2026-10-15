import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((643256879:ℚ)/1000000000),((6745402757:ℚ)/10000000000),((-12556208271:ℚ)/49600000000),((-323256879:ℚ)/2060000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((224650139:ℚ)/400000000),((356247918696949767639883301558716317035027754154110161:ℚ)/1693726850000000000000000000000000000000000000000000000),((-14465291734378494985981:ℚ)/591462400000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3336291191:ℚ)/5000000000),((1373076101:ℚ)/2000000000),((-2583228303:ℚ)/10300000000),((-1736291191:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4991884181:ℚ)/10000000000),((38200191646769452501519691780437336917209569718386510953:ℚ)/185773479448437500000000000000000000000000000000000000000),((-548107598872570253085421:ℚ)/14786560000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((1698129963:ℚ)/2500000000),((6985313913:ℚ)/10000000000),((-13275941739:ℚ)/52450000000),((-898129963:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((290721091:ℚ)/625000000),((51257765569009471352024562829600191299122937536741747147:ℚ)/249585462337500000000000000000000000000000000000000000000),((-481495298119702858800287:ℚ)/11089920000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((3456207229:ℚ)/5000000000),((3522632369:ℚ)/5000000000),((-2242632369:ℚ)/8900000000),((-1856207229:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4286487459:ℚ)/10000000000),((552484235726963344543426375368109122639815354028916029:ℚ)/2718203048324584960937500000000000000000000000000000000),((-736314105324406195075781:ℚ)/14786560000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6972346409:ℚ)/10000000000),((7105205353:ℚ)/10000000000),((-13635616059:ℚ)/53875000000),((-3772346409:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2046319369:ℚ)/5000000000),((5623470846226985755236998063657463426303880337244632433551:ℚ)/27678076589650000000000000000000000000000000000000000000000),((-3134550190267988583314221:ℚ)/59146240000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7032268491:ℚ)/10000000000),((716513603:ℚ)/1000000000),((-1381540809:ℚ)/5435000000),((-3832268491:ℚ)/21930000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1944872119:ℚ)/5000000000),((1212711778177908106335431304656929224916579689867229842071:ℚ)/5970960668207812500000000000000000000000000000000000000000),((-9972840437334048695204063:ℚ)/177438720000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7092180963:ℚ)/10000000000),((1806264257:ℚ)/2500000000),((-1166264257:ℚ)/4568750000),((-3892180963:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((29410411:ℚ)/80000000),((470615146201590946251729381153803068131902950091215454251:ℚ)/2317896517256250000000000000000000000000000000000000000000),((-10543340640074077700598287:ℚ)/177438720000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((3576042039:ℚ)/5000000000),((36424843:ℚ)/50000000),((-70874529:ℚ)/276500000),((-1976042039:ℚ)/11155000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3450347657:ℚ)/10000000000),((60860737543317648902924978184225231300005793063629943287:ℚ)/299842983018701171875000000000000000000000000000000000000),((-2778788230653998240282183:ℚ)/44359680000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((45074863:ℚ)/62500000),((7344870989:ℚ)/10000000000),((-14354612967:ℚ)/55775000000),((-25074863:ℚ)/140625000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((200577241:ℚ)/625000000),((92209497319463349642102098594959674010533969570599:ℚ)/454410631209611892700195312500000000000000000000000),((-152191132371086936829:ℚ)/2310400000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((7271863203:ℚ)/10000000000),((1866162287:ℚ)/2500000000),((-1226162287:ℚ)/4687500000),((-4071863203:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2949244479:ℚ)/10000000000),((4178111910465376970584296867959334920841842293730562179:ℚ)/20416281600000000000000000000000000000000000000000000000),((-12262720378546568881438607:ℚ)/177438720000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((3695803857:ℚ)/5000000000),((7704105081:ℚ)/10000000000),((-15432315243:ℚ)/57200000000),((-2095803857:ℚ)/11820000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2347180089:ℚ)/10000000000),((8525535353997285889049229653497540456346141460709874159:ℚ)/40998312712500000000000000000000000000000000000000000000),((-3353888881045160011003127:ℚ)/44359680000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((3815499837:ℚ)/5000000000),((3971718877:ℚ)/5000000000),((-2691718877:ℚ)/9850000000),((-2215499837:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((1392641533052512295788129499533375893675608654708439282707:ℚ)/6707288550000000000000000000000000000000000000000000000000),((-44538299:ℚ)/512000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((157405449:ℚ)/200000000),((2105444327:ℚ)/2500000000),((-4396332981:ℚ)/15250000000),((-93405449:ℚ)/518400000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3780671539321305236048867116299732706695757585001647:ℚ)/17704496332800000000000000000000000000000000000000000),((-44538299:ℚ)/512000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((2087125741:ℚ)/2500000000),((5165969269:ℚ)/5000000000),((-3885969269:ℚ)/10800000000),((-1287125741:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((21118758856576930149512246263585947173829030820265544263:ℚ)/86400000000000000000000000000000000000000000000000000000),((-44538299:ℚ)/512000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10258333191:ℚ)/10000000000),((14143828021:ℚ)/10000000000),((-34751484063:ℚ)/80000000000),((-7058333191:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((113872605601346726139806185788045910261598186971617870317:ℚ)/403671859200000000000000000000000000000000000000000000000),((-44538299:ℚ)/512000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC11
#check @N11Formalization.C450Source26GroupedC11.bound
#print axioms N11Formalization.C450Source26GroupedC11.valid0
#print axioms N11Formalization.C450Source26GroupedC11.valid1
#print axioms N11Formalization.C450Source26GroupedC11.valid2
#print axioms N11Formalization.C450Source26GroupedC11.valid3
#print axioms N11Formalization.C450Source26GroupedC11.valid4
#print axioms N11Formalization.C450Source26GroupedC11.valid5
#print axioms N11Formalization.C450Source26GroupedC11.valid6
#print axioms N11Formalization.C450Source26GroupedC11.valid7
#print axioms N11Formalization.C450Source26GroupedC11.valid8
#print axioms N11Formalization.C450Source26GroupedC11.valid9
#print axioms N11Formalization.C450Source26GroupedC11.valid10
#print axioms N11Formalization.C450Source26GroupedC11.valid11
#print axioms N11Formalization.C450Source26GroupedC11.valid12
#print axioms N11Formalization.C450Source26GroupedC11.valid13
#print axioms N11Formalization.C450Source26GroupedC11.valid14
#print axioms N11Formalization.C450Source26GroupedC11.bound
#print axioms N11Formalization.C450Source26GroupedC11.endpoint_checks
