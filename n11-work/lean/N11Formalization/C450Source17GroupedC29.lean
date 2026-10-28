import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((566876401:ℚ)/1000000000),((1242638361:ℚ)/2000000000),((646876401:ℚ)/890000000),((18202298693:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3644631421:ℚ)/5000000000),((-2398794769592693748477622350629653:ℚ)/44060562500000000000000000000000000),((-8054358915990352585299:ℚ)/25600000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((49156519:ℚ)/80000000),((3225549097:ℚ)/5000000000),((166669557:ℚ)/221200000),((15684046087:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6292054161:ℚ)/10000000000),((-2154564738579181819155687967577536907475340238661:ℚ)/33822475400000000000000000000000000000000000000000),((-18059782101820464266479131:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((3191211969:ℚ)/5000000000),((83612219:ℚ)/125000000),((10773635907:ℚ)/14300000000),((1214958847:ℚ)/1382500000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2869475959:ℚ)/5000000000),((-584036279729803890026722225492637363255916150074116859:ℚ)/9138146875000000000000000000000000000000000000000000000),((-11216478443670042007449:ℚ)/36100000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((827532387:ℚ)/1250000000),((6807907867:ℚ)/10000000000),((2782597161:ℚ)/3634375000),((98742802271:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2566928133:ℚ)/5000000000),((-2552151166666595027388702762117970778357482811060017:ℚ)/37504142451286315917968750000000000000000000000000000),((-71557800416127605962611651:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3369584223:ℚ)/5000000000),((3463416201:ℚ)/5000000000),((3769584223:ℚ)/4925000000),((50144410613:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1201418913:ℚ)/2500000000),((-19050677029583498370562526688193930446493103836412533:ℚ)/279981921386718750000000000000000000000000000000000000),((-17832396462911119440301659:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3429036331:ℚ)/5000000000),((7045751403:ℚ)/10000000000),((11487108993:ℚ)/15012500000),((101834768239:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((69615663:ℚ)/156250000),((-719322472027212386317452377741360632188238856084695809:ℚ)/10573264166259765625000000000000000000000000000000000000),((-71100817893280967030956131:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((697697199:ℚ)/1000000000),((710520891:ℚ)/1000000000),((777697199:ℚ)/1008750000),((10260771583:ℚ)/12010000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((4077316951:ℚ)/10000000000),((-8311454317299674601732561345633520698642991052589:ℚ)/118805596923828125000000000000000000000000000000000),((-709862262583474989728979:ℚ)/2310400000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((7036419893:ℚ)/10000000000),((716466513:ℚ)/1000000000),((23509259679:ℚ)/30500000000),((10338064669:ℚ)/12105000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1937657677:ℚ)/5000000000),((-6200405437280856282716321045136900419525500433363243583:ℚ)/88664453125000000000000000000000000000000000000000000000),((-708714961177566295240971:ℚ)/2310400000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((7095866659:ℚ)/10000000000),((291342953:ℚ)/400000000),((7895866659:ℚ)/10325000000),((4197058389:ℚ)/4880000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((732556847:ℚ)/2000000000),((-58477556285271353803952574053748775217283692362520323:ℚ)/859924279785156250000000000000000000000000000000000000),((-113026592210713441172331:ℚ)/369664000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3607378441:ℚ)/5000000000),((7402477717:ℚ)/10000000000),((12022135323:ℚ)/15725000000),((106472210321:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3197624519:ℚ)/10000000000),((-806738921431715027578805105007206920759358353359291:ℚ)/11866483163833618164062500000000000000000000000000000),((-70411189562353782881113251:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((3666821431:ℚ)/5000000000),((7640271939:ℚ)/10000000000),((4066821431:ℚ)/5400000000),((109563535207:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2655320781:ℚ)/10000000000),((-391498673450519515949764642614025256685046687931863:ℚ)/6075000000000000000000000000000000000000000000000000),((-38796207:ℚ)/128000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((3785701421:ℚ)/5000000000),((9542121899:ℚ)/10000000000),((12557104263:ℚ)/20000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((433886281:ℚ)/5000000000),((-46546517703476901618543776650949470914049614586801911:ℚ)/1562500000000000000000000000000000000000000000000000000),((-38796207:ℚ)/128000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((4736518787:ℚ)/5000000000),((133442923:ℚ)/100000000),((5136518787:ℚ)/9200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-856261354106506597645469881533737:ℚ)/97336000000000000000000000000000000),((-38796207:ℚ)/128000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC29
#check @N11Formalization.C450Source17GroupedC29.bound
#print axioms N11Formalization.C450Source17GroupedC29.valid0
#print axioms N11Formalization.C450Source17GroupedC29.valid1
#print axioms N11Formalization.C450Source17GroupedC29.valid2
#print axioms N11Formalization.C450Source17GroupedC29.valid3
#print axioms N11Formalization.C450Source17GroupedC29.valid4
#print axioms N11Formalization.C450Source17GroupedC29.valid5
#print axioms N11Formalization.C450Source17GroupedC29.valid6
#print axioms N11Formalization.C450Source17GroupedC29.valid7
#print axioms N11Formalization.C450Source17GroupedC29.valid8
#print axioms N11Formalization.C450Source17GroupedC29.valid9
#print axioms N11Formalization.C450Source17GroupedC29.valid10
#print axioms N11Formalization.C450Source17GroupedC29.valid11
#print axioms N11Formalization.C450Source17GroupedC29.valid12
#print axioms N11Formalization.C450Source17GroupedC29.bound
#print axioms N11Formalization.C450Source17GroupedC29.endpoint_checks
