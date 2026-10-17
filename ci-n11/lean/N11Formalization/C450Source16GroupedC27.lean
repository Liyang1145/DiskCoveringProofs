import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((1443042767:ℚ)/2500000000),((3155335007:ℚ)/5000000000),((1667042767:ℚ)/2670000000),((39508685077:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7082580403:ℚ)/10000000000),((-1454002282190910308663412097523:ℚ)/59481759375000000000000000000000),((-1379078289003300029912893:ℚ)/4864000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((781033039:ℚ)/1250000000),((6548663369:ℚ)/10000000000),((893033039:ℚ)/1382500000),((81635297059:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((605636277:ℚ)/1000000000),((-19102723052005545076331543117030208001480659616211:ℚ)/619308021240234375000000000000000000000000000000000),((-5520933151978907738568077:ℚ)/19456000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((3243127207:ℚ)/5000000000),((3393311927:ℚ)/5000000000),((3691127207:ℚ)/5720000000),((42126431197:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1370545329:ℚ)/2500000000),((-35058970382042522330902670458812477327348614443957:ℚ)/1124695000000000000000000000000000000000000000000000),((-1380108226646463348291853:ℚ)/4864000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6724211863:ℚ)/10000000000),((6905592781:ℚ)/10000000000),((7620211863:ℚ)/11630000000),((85561520591:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4848074123:ℚ)/10000000000),((-1042538655581391773620967475146345622532132369967721:ℚ)/30723393496093750000000000000000000000000000000000000),((-5522572263184525139564677:ℚ)/19456000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3421589673:ℚ)/5000000000),((140491093:ℚ)/200000000),((3869589673:ℚ)/5910000000),((1737402023:ℚ)/2326000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((281291333:ℚ)/625000000),((-411158952039977291893116964200187717799682557855317:ℚ)/12095219003906250000000000000000000000000000000000000),((-2208880401264268635093:ℚ)/7782400000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6962139819:ℚ)/10000000000),((3571754899:ℚ)/5000000000),((7858139819:ℚ)/12010000000),((44089303889:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4126257133:ℚ)/10000000000),((-13822149933633504791554159969307401238754647307452351:ℚ)/406013343984375000000000000000000000000000000000000000),((-1380445343021357663156357:ℚ)/4864000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((442568351:ℚ)/625000000),((7262458541:ℚ)/10000000000),((498568351:ℚ)/762500000),((89487043951:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3716680833:ℚ)/10000000000),((-1180476751601075236659786566245114520672617228153:ℚ)/34634552001953125000000000000000000000000000000000),((-5521313377224723533371717:ℚ)/19456000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((900005131:ℚ)/1250000000),((7381401173:ℚ)/10000000000),((1012005131:ℚ)/1548750000),((90795412903:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3182286:ℚ)/9765625),((-825074016307593921431689637013300127275312029711:ℚ)/24185370368957519531250000000000000000000000000000),((-5520797025409239578420053:ℚ)/19456000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((7318982411:ℚ)/10000000000),((7500337973:ℚ)/10000000000),((8214982411:ℚ)/12580000000),((92103717703:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1363930777:ℚ)/5000000000),((-305000936375858515721971159653171418009841934061:ℚ)/8934763793945312500000000000000000000000000000000),((-5520232323065268811589653:ℚ)/19456000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((371895899:ℚ)/500000000),((241818597:ℚ)/312500000),((138898633:ℚ)/216000000),((2960004567:ℚ)/3931250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2068952371:ℚ)/10000000000),((-931098319336524305057930113374676899712167277:ℚ)/29160000000000000000000000000000000000000000000),((-2760060329234959:ℚ)/9728000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((3837886379:ℚ)/5000000000),((9640440433:ℚ)/10000000000),((4285886379:ℚ)/8000000000),((115644844763:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-24564361151390459779121094399271519718576980939893:ℚ)/2500000000000000000000000000000000000000000000000000),((-726773:ℚ)/2560000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9578003301:ℚ)/10000000000),((840192147:ℚ)/625000000),((10474003301:ℚ)/22080000000),((9842113617:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((179348270838567380248037:ℚ)/30470400000000000000000000),((-726773:ℚ)/2560000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC27
#check @N11Formalization.C450Source16GroupedC27.bound
#print axioms N11Formalization.C450Source16GroupedC27.valid0
#print axioms N11Formalization.C450Source16GroupedC27.valid1
#print axioms N11Formalization.C450Source16GroupedC27.valid2
#print axioms N11Formalization.C450Source16GroupedC27.valid3
#print axioms N11Formalization.C450Source16GroupedC27.valid4
#print axioms N11Formalization.C450Source16GroupedC27.valid5
#print axioms N11Formalization.C450Source16GroupedC27.valid6
#print axioms N11Formalization.C450Source16GroupedC27.valid7
#print axioms N11Formalization.C450Source16GroupedC27.valid8
#print axioms N11Formalization.C450Source16GroupedC27.valid9
#print axioms N11Formalization.C450Source16GroupedC27.valid10
#print axioms N11Formalization.C450Source16GroupedC27.valid11
#print axioms N11Formalization.C450Source16GroupedC27.bound
#print axioms N11Formalization.C450Source16GroupedC27.endpoint_checks
