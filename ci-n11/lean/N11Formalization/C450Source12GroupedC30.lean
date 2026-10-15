import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((5811339643:ℚ)/10000000000),((253837029:ℚ)/400000000),((81947415359:ℚ)/106800000000),((1917659203:ℚ)/1984000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((700298347:ℚ)/1000000000),((-547244977972821539964853189113602727:ℚ)/14099380000000000000000000000000000000),((-405798071711540981836973:ℚ)/1774387200000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1257320051:ℚ)/2000000000),((6583565791:ℚ)/10000000000),((17625160663:ℚ)/22120000000),((49604960537:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5967181409:ℚ)/10000000000),((-186358706112060967362558494669059770677471965698641089:ℚ)/4227809425000000000000000000000000000000000000000000000),((-84059416543942929433353831:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((40776357:ℚ)/62500000),((6821196543:ℚ)/10000000000),((570092641:ℚ)/715000000),((51268375801:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1346392819:ℚ)/2500000000),((-6309625846256844488315595539684481563480915083663:ℚ)/142783544921875000000000000000000000000000000000000),((-250732586383674671261636597:ℚ)/1108992000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((845228277:ℚ)/1250000000),((6940008713:ℚ)/10000000000),((11787967601:ℚ)/14537500000),((4736369181:ℚ)/5200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((592597593:ℚ)/1250000000),((-13973780503996100266235408823376101522154096960695767:ℚ)/300033139610290527343750000000000000000000000000000000),((-83336569582905942839125719:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((6880628089:ℚ)/10000000000),((3499707021:ℚ)/5000000000),((95848165157:ℚ)/117250000000),((26257949147:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((4386030389:ℚ)/10000000000),((-1073544876973639560987794540963037948968582754628152077:ℚ)/22487467956542968750000000000000000000000000000000000000),((-62412064538175656073699773:ℚ)/277248000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3470014197:ℚ)/5000000000),((3529409441:ℚ)/5000000000),((48310184561:ℚ)/59100000000),((26465866087:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4198216971:ℚ)/10000000000),((-106902864221451472073680208527204170663035314112827207:ℚ)/2239855371093750000000000000000000000000000000000000000),((-20773899967785729668150631:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6999428293:ℚ)/10000000000),((7118223247:ℚ)/10000000000),((97392567809:ℚ)/119150000000),((53347562729:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1000536479:ℚ)/2500000000),((-31528583586426490720373425415457943817213053880876498063:ℚ)/660757611669921875000000000000000000000000000000000000000),((-82975111015325563052668359:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((3529413897:ℚ)/5000000000),((7177627147:ℚ)/10000000000),((49082380661:ℚ)/60050000000),((53763390029:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3796534273:ℚ)/10000000000),((-252195555008781097543352118904807023715221192546989747:ℚ)/5286632083129882812500000000000000000000000000000000000),((-82854619463252363868894959:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7118226907:ℚ)/10000000000),((113078603:ℚ)/156250000),((98936949791:ℚ)/121050000000),((846550221:ℚ)/938281250),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3579734479:ℚ)/10000000000),((-135989571058465582502450360663294701241966524793130779:ℚ)/2851334326171875000000000000000000000000000000000000000),((-20198761033868268016959:ℚ)/90250000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((3588812821:ℚ)/5000000000),((1459286719:ℚ)/2000000000),((49854566673:ℚ)/61000000000),((3639669011:ℚ)/4035000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((837392647:ℚ)/2500000000),((-69307349059020172519183895631147796372786546483867179:ℚ)/1453515625000000000000000000000000000000000000000000000),((-3304545127338196415555111:ℚ)/14786560000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7237024007:ℚ)/10000000000),((1838959041:ℚ)/2500000000),((100481312091:ℚ)/122950000000),((13752713287:ℚ)/15250000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((3103065781:ℚ)/10000000000),((-8652672844905403387097454974120021764587946971589085637:ℚ)/181503766833496093750000000000000000000000000000000000000),((-15467461577493109805413493:ℚ)/69312000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((729642201:ℚ)/1000000000),((741523831:ℚ)/1000000000),((10125348613:ℚ)/12390000000),((5542666817:ℚ)/6147500000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((283595729:ℚ)/1000000000),((-3934631062963227693794192244927331937364817965869171:ℚ)/82552730859375000000000000000000000000000000000000000),((-823726258620143990026711:ℚ)/3696640000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((7355819661:ℚ)/10000000000),((1883510343:ℚ)/2500000000),((102025655593:ℚ)/125800000000),((14064572401:ℚ)/15487500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((127087621:ℚ)/500000000),((-35372850865444640390782542579090956477219181625365391:ℚ)/759454922485351562500000000000000000000000000000000000),((-15399677313237836458576997:ℚ)/69312000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((1494922787:ℚ)/2000000000),((310865713:ℚ)/400000000),((20713996231:ℚ)/25920000000),((2316859991:ℚ)/2516000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((181899599:ℚ)/1000000000),((-138548972782339321712868627613403229037246806782539:ℚ)/3110400000000000000000000000000000000000000000000000),((-28392589:ℚ)/128000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((7712198587:ℚ)/10000000000),((9672280883:ℚ)/10000000000),((106658581631:ℚ)/160000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-2442207247331736513452866872810144666632287429159093073:ℚ)/100000000000000000000000000000000000000000000000000000000),((-28392589:ℚ)/128000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((961273099:ℚ)/1000000000),((13473029753:ℚ)/10000000000),((13136550287:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-246581791046529624317225653884083:ℚ)/18688512000000000000000000000000000),((-28392589:ℚ)/128000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC30
#check @N11Formalization.C450Source12GroupedC30.bound
#print axioms N11Formalization.C450Source12GroupedC30.valid0
#print axioms N11Formalization.C450Source12GroupedC30.valid1
#print axioms N11Formalization.C450Source12GroupedC30.valid2
#print axioms N11Formalization.C450Source12GroupedC30.valid3
#print axioms N11Formalization.C450Source12GroupedC30.valid4
#print axioms N11Formalization.C450Source12GroupedC30.valid5
#print axioms N11Formalization.C450Source12GroupedC30.valid6
#print axioms N11Formalization.C450Source12GroupedC30.valid7
#print axioms N11Formalization.C450Source12GroupedC30.valid8
#print axioms N11Formalization.C450Source12GroupedC30.valid9
#print axioms N11Formalization.C450Source12GroupedC30.valid10
#print axioms N11Formalization.C450Source12GroupedC30.valid11
#print axioms N11Formalization.C450Source12GroupedC30.valid12
#print axioms N11Formalization.C450Source12GroupedC30.valid13
#print axioms N11Formalization.C450Source12GroupedC30.valid14
#print axioms N11Formalization.C450Source12GroupedC30.valid15
#print axioms N11Formalization.C450Source12GroupedC30.bound
#print axioms N11Formalization.C450Source12GroupedC30.endpoint_checks
