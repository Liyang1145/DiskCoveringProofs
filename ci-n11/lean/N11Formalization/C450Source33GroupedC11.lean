import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1618645273:ℚ)/2500000000),((6686335601:ℚ)/10000000000),((-10139006803:ℚ)/49600000000),((-198215091:ℚ)/1685000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((275579109:ℚ)/500000000),((50976013587467413511951946097946357369:ℚ)/381324800000000000000000000000000000000),((7825478860379177748708023:ℚ)/184832000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((1319098289:ℚ)/2000000000),((850899471:ℚ)/1250000000),((-1312698413:ℚ)/6318750000),((-499898289:ℚ)/4120000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2599913037:ℚ)/5000000000),((1331673120984395902470090779403314566202576459628349:ℚ)/9854930219650268554687500000000000000000000000000000),((4130153468902750024160327:ℚ)/118292480000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((671631999:ℚ)/1000000000),((6867596167:ℚ)/10000000000),((-10682788501:ℚ)/51500000000),((-262031999:ℚ)/2079000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((304394297:ℚ)/625000000),((44734165030963695315017077260589684357470884660949093:ℚ)/333473815917968750000000000000000000000000000000000000),((811088281892803192978087:ℚ)/29573120000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1355341007:ℚ)/2000000000),((86599719:ℚ)/125000000),((-135799157:ℚ)/649687500),((-536141007:ℚ)/4196000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((58721447:ℚ)/125000000),((1299450011630483260281717866891127724327002683:ℚ)/9635868072509765625000000000000000000000000000),((2798579701890352230696263:ℚ)/118292480000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((273482853:ℚ)/400000000),((1397668071:ℚ)/2000000000),((-2209004213:ℚ)/10490000000),((-109642853:ℚ)/846800000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((564887581:ℚ)/1250000000),((97794764422363235748445954857260047234744549023795661:ℚ)/721450405625000000000000000000000000000000000000000000),((94035520106817170819983:ℚ)/4731699200000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((3448709691:ℚ)/5000000000),((7048685183:ℚ)/10000000000),((-11226055549:ℚ)/52925000000),((-1400709691:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1083428301:ℚ)/2500000000),((9467279851827026017756735697921673757414219277154179239:ℚ)/69490251071777343750000000000000000000000000000000000000),((11882975304086696363472847:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((6957749707:ℚ)/10000000000),((444313281:ℚ)/625000000),((-712939843:ℚ)/3337500000),((-2861749707:ℚ)/21550000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((828127617:ℚ)/2000000000),((9543613941978961657924648879240890653653831218064297:ℚ)/69705186767578125000000000000000000000000000000000000),((100397641581113126088983:ℚ)/8192000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3509031393:ℚ)/5000000000),((448082673:ℚ)/625000000),((-724248019:ℚ)/3367187500),((-1461031393:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((196936947:ℚ)/500000000),((3282710572533606243986862333223140263012370849133367:ℚ)/23860630691051483154296875000000000000000000000000000),((6226773992847074131033063:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1769589771:ℚ)/2500000000),((903702057:ℚ)/1250000000),((-1471106171:ℚ)/6793750000),((-17339297:ℚ)/127500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1863287833:ℚ)/5000000000),((5079513767728866499672830532103532496016264249962169:ℚ)/36745991792678833007812500000000000000000000000000000),((845156207906102782608367:ℚ)/184832000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7138639051:ℚ)/10000000000),((7289893999:ℚ)/10000000000),((-11949681997:ℚ)/54825000000),((-3042639051:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((875569241:ℚ)/2500000000),((332645546094156973952562652219434982287373309974327167:ℚ)/2395231435546875000000000000000000000000000000000000000),((2089715961390619050258287:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((89986289:ℚ)/125000000),((370520117:ℚ)/500000000),((-87937193:ℚ)/395000000),((-12928763:ℚ)/93750000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3263334721:ℚ)/10000000000),((5456825991169243435856715950249043314958520808281:ℚ)/38518671875000000000000000000000000000000000000000),((-1467389864840453871673:ℚ)/462080000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((292775409:ℚ)/400000000),((1506170203:ℚ)/2000000000),((-2534510609:ℚ)/11250000000),((-128935409:ℚ)/915200000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2725893573:ℚ)/10000000000),((127134438537745179898473541626890417674827106228879297:ℚ)/889892578125000000000000000000000000000000000000000000),((-51997053287512596970553:ℚ)/4731699200000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((7439808573:ℚ)/10000000000),((4006053141:ℚ)/5000000000),((-7058159423:ℚ)/28600000000),((-3343808573:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((2056807437:ℚ)/10000000000),((1713755967254457263169644067735612978488271901516842437:ℚ)/10965776250000000000000000000000000000000000000000000000),((-55798391203443136970985377:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((990121341:ℚ)/1250000000),((530788441:ℚ)/625000000),((-972365323:ℚ)/3812500000),((-478121341:ℚ)/3240000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1383164828194609913193078353278875587480615080087739:ℚ)/8658638000488281250000000000000000000000000000000000),((-30162839:ℚ)/1024000000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((2100349423:ℚ)/2500000000),((5204675217:ℚ)/5000000000),((-10654025651:ℚ)/32400000000),((-1076349423:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((811728568355229662027849151154347377626333204637839649:ℚ)/3985807500000000000000000000000000000000000000000000000),((-30162839:ℚ)/1024000000)⟩
theorem valid14 : Valid source33 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10317885501:ℚ)/10000000000),((14228890867:ℚ)/10000000000),((-32766672601:ℚ)/80000000000),((-6221885501:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((16826376705352542030765911777201255903:ℚ)/64000000000000000000000000000000000000),((-30162839:ℚ)/1024000000)⟩
theorem valid15 : Valid source33 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC11
#check @N11Formalization.C450Source33GroupedC11.bound
#print axioms N11Formalization.C450Source33GroupedC11.valid0
#print axioms N11Formalization.C450Source33GroupedC11.valid1
#print axioms N11Formalization.C450Source33GroupedC11.valid2
#print axioms N11Formalization.C450Source33GroupedC11.valid3
#print axioms N11Formalization.C450Source33GroupedC11.valid4
#print axioms N11Formalization.C450Source33GroupedC11.valid5
#print axioms N11Formalization.C450Source33GroupedC11.valid6
#print axioms N11Formalization.C450Source33GroupedC11.valid7
#print axioms N11Formalization.C450Source33GroupedC11.valid8
#print axioms N11Formalization.C450Source33GroupedC11.valid9
#print axioms N11Formalization.C450Source33GroupedC11.valid10
#print axioms N11Formalization.C450Source33GroupedC11.valid11
#print axioms N11Formalization.C450Source33GroupedC11.valid12
#print axioms N11Formalization.C450Source33GroupedC11.valid13
#print axioms N11Formalization.C450Source33GroupedC11.valid14
#print axioms N11Formalization.C450Source33GroupedC11.valid15
#print axioms N11Formalization.C450Source33GroupedC11.bound
#print axioms N11Formalization.C450Source33GroupedC11.endpoint_checks
