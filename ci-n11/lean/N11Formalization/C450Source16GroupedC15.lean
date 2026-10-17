import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((6208513387:ℚ)/10000000000),((3361701033:ℚ)/5000000000),((-1121701033:ℚ)/24800000000),((3391486613:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((768454849:ℚ)/1250000000),((167247274973640359807235697256804263:ℚ)/3050598400000000000000000000000000000),((-47857116124778323971292339:ℚ)/778240000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((3342792389:ℚ)/5000000000),((6842618791:ℚ)/10000000000),((-787539597:ℚ)/17800000000),((1457207611:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4956027861:ℚ)/10000000000),((1892681005706956476110334711956073000001862811279093161:ℚ)/35689055625000000000000000000000000000000000000000000000),((-13734966961842085283194451:ℚ)/194560000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((1701201773:ℚ)/2500000000),((1740454847:ℚ)/2500000000),((-620454847:ℚ)/13587500000),((698798227:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((923072819:ℚ)/2000000000),((15519487174300114095518650538866209535555081184028377:ℚ)/293967934341430664062500000000000000000000000000000000),((-3544430568956148741976899:ℚ)/48640000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((1384802617:ℚ)/2000000000),((3540502341:ℚ)/5000000000),((-1300502341:ℚ)/27650000000),((76456769:ℚ)/3160000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4249621147:ℚ)/10000000000),((907251483783967188013246658220053522517227848180319:ℚ)/17256365000000000000000000000000000000000000000000000),((-2339282857664975107936859:ℚ)/31129600000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((7043203589:ℚ)/10000000000),((7140591831:ℚ)/10000000000),((-2660591831:ℚ)/56250000000),((2556796411:ℚ)/112500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((60181673:ℚ)/156250000),((5816516290011812492614004625847839683430405232824172363:ℚ)/111236572265625000000000000000000000000000000000000000000),((-60253427062829202989956051:ℚ)/778240000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((3551396639:ℚ)/5000000000),((7200175439:ℚ)/10000000000),((-2720175439:ℚ)/56725000000),((1248603361:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1818625693:ℚ)/5000000000),((29773437695073414080667073481696554420155545326400953:ℚ)/570392143994140625000000000000000000000000000000000000),((-15284793363212038879933451:ℚ)/194560000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((3581189691:ℚ)/5000000000),((7259755593:ℚ)/10000000000),((-2779755593:ℚ)/57200000000),((1218810309:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((341007079:ℚ)/1000000000),((14652322708635846761065088585392328802403227539101281:ℚ)/281173750000000000000000000000000000000000000000000000),((-46518725531911922702762233:ℚ)/583680000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7221961991:ℚ)/10000000000),((3659666189:ℚ)/5000000000),((-473222063:ℚ)/9612500000),((2378038009:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3167326239:ℚ)/10000000000),((83181112099094359929286977685460920391122158001982531:ℚ)/1598753703515625000000000000000000000000000000000000000),((-62910810151883940600354011:ℚ)/778240000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7281541191:ℚ)/10000000000),((7438476169:ℚ)/10000000000),((-2958476169:ℚ)/58150000000),((2318458809:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1452556811:ℚ)/5000000000),((1598674131111733648225983256941292537526433534782910057:ℚ)/30723393496093750000000000000000000000000000000000000000),((-191390109125801675547401233:ℚ)/2334720000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((3700344847:ℚ)/5000000000),((383836339:ℚ)/500000000),((-159836339:ℚ)/2955000000),((1099655153:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2295233069:ℚ)/10000000000),((2518414923077489582385453246571913719716388616064556747:ℚ)/48380876015625000000000000000000000000000000000000000000),((-16392161000798308559683179:ℚ)/194560000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((1909737321:ℚ)/2500000000),((1019136923:ℚ)/1250000000),((-459136923:ℚ)/7625000000),((490262679:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((28884126018142502565741868245423760999353177742813543:ℚ)/554152832031250000000000000000000000000000000000000000),((-90175827:ℚ)/1024000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((2028833563:ℚ)/2500000000),((10057265527:ℚ)/10000000000),((-1859088509:ℚ)/21600000000),((371166437:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((26690158996371029924224154089776074856555164383411567:ℚ)/498225937500000000000000000000000000000000000000000000),((-90175827:ℚ)/1024000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((10019369031:ℚ)/10000000000),((277243087:ℚ)/200000000),((-187643087:ℚ)/1600000000),((-139789677:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((458187853498477865511455747102670805821156654884004331:ℚ)/7786880000000000000000000000000000000000000000000000000),((-90175827:ℚ)/1024000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC15
#check @N11Formalization.C450Source16GroupedC15.bound
#print axioms N11Formalization.C450Source16GroupedC15.valid0
#print axioms N11Formalization.C450Source16GroupedC15.valid1
#print axioms N11Formalization.C450Source16GroupedC15.valid2
#print axioms N11Formalization.C450Source16GroupedC15.valid3
#print axioms N11Formalization.C450Source16GroupedC15.valid4
#print axioms N11Formalization.C450Source16GroupedC15.valid5
#print axioms N11Formalization.C450Source16GroupedC15.valid6
#print axioms N11Formalization.C450Source16GroupedC15.valid7
#print axioms N11Formalization.C450Source16GroupedC15.valid8
#print axioms N11Formalization.C450Source16GroupedC15.valid9
#print axioms N11Formalization.C450Source16GroupedC15.valid10
#print axioms N11Formalization.C450Source16GroupedC15.valid11
#print axioms N11Formalization.C450Source16GroupedC15.valid12
#print axioms N11Formalization.C450Source16GroupedC15.bound
#print axioms N11Formalization.C450Source16GroupedC15.endpoint_checks
