import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((6133513387:ℚ)/10000000000),((3325733943:ℚ)/5000000000),((112:ℚ)/1335),((8125733943:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6316721597:ℚ)/10000000000),((1362121211353191394711825920858883492717:ℚ)/27184263667200000000000000000000000000000),((-68767507021898567215483343:ℚ)/583680000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((3305292389:ℚ)/5000000000),((6889779117:ℚ)/10000000000),((32:ℚ)/395),((5496593039:ℚ)/35600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((128992889:ℚ)/250000000),((3179552772216839493811538237898730614212326054907679107149:ℚ)/65995672935000000000000000000000000000000000000000000000000),((-296426559320850603178346423:ℚ)/2334720000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((1369802617:ℚ)/2000000000),((7008914081:ℚ)/10000000000),((448:ℚ)/5625),((16608914081:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1120746021:ℚ)/2500000000),((58003155815407080546851375495806767767246927169654686239:ℚ)/1223044869375000000000000000000000000000000000000000000000),((-102366061590314332234741109:ℚ)/778240000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((6968203589:ℚ)/10000000000),((3564018099:ℚ)/5000000000),((56:ℚ)/715),((2788006033:ℚ)/18750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2053157813:ℚ)/5000000000),((496851726689632689728710798136865464727108050921438407849:ℚ)/10530910491943359375000000000000000000000000000000000000000),((-78099116889461355153094007:ℚ)/583680000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((3543689691:ℚ)/5000000000),((3593796319:ℚ)/5000000000),((896:ℚ)/11535),((8393796319:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((230865009:ℚ)/625000000),((23382346906676115723127106326242324514879619732658305125633:ℚ)/498825569921250000000000000000000000000000000000000000000000),((-26477458407482104848609909:ℚ)/194560000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7146961991:ℚ)/10000000000),((72471461:ℚ)/100000000),((448:ℚ)/5815),((168471461:ℚ)/1153500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((138808753:ℚ)/400000000),((101143985864783871670137050807485383263120176450721671:ℚ)/2162424698010425390625000000000000000000000000000000000),((-10679244062700263642349:ℚ)/77824000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7206541191:ℚ)/10000000000),((7366244381:ℚ)/10000000000),((224:ℚ)/2955),((16966244381:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((646367523:ℚ)/2000000000),((167255418524196816182654295726088956514020272893725463301431:ℚ)/3577032534569707031250000000000000000000000000000000000000000),((-5666446907914878890909711:ℚ)/40960000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((3662844847:ℚ)/5000000000),((1871332899:ℚ)/2500000000),((448:ℚ)/6005),((1423777633:ℚ)/9850000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((269490997:ℚ)/1000000000),((15048376465533838234938088093126899006975655134012584559707:ℚ)/323076962712099609375000000000000000000000000000000000000000),((-20517516278582975555246807:ℚ)/145920000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((3722412763:ℚ)/5000000000),((950551033:ℚ)/1250000000),((112:ℚ)/1525),((2150551033:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1012115487:ℚ)/5000000000),((45655458350978495014881815510808228855099587453199805769:ℚ)/983577899066314697265625000000000000000000000000000000000),((-13898922076096263:ℚ)/97280000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((1890987321:ℚ)/2500000000),((8080618791:ℚ)/10000000000),((28:ℚ)/405),((17680618791:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((487199661:ℚ)/5000000000),((10866500096079507189102836694262765245902133894573920035447:ℚ)/232690990781250000000000000000000000000000000000000000000000),((-7061273605181821:ℚ)/48640000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((2010083563:ℚ)/2500000000),((998430769:ℚ)/1000000000),((7:ℚ)/125),((1958430769:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1516458325415590450675876616756855298270993849169451:ℚ)/31886460000000000000000000000000000000000000000000000),((-149370773:ℚ)/1024000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9944554207:ℚ)/10000000000),((6894316501:ℚ)/5000000000),((14:ℚ)/345),((11694316501:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((406365310388104681950727160786954338319:ℚ)/7617600000000000000000000000000000000000),((-149370773:ℚ)/1024000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC17
#check @N11Formalization.C450Source16GroupedC17.bound
#print axioms N11Formalization.C450Source16GroupedC17.valid0
#print axioms N11Formalization.C450Source16GroupedC17.valid1
#print axioms N11Formalization.C450Source16GroupedC17.valid2
#print axioms N11Formalization.C450Source16GroupedC17.valid3
#print axioms N11Formalization.C450Source16GroupedC17.valid4
#print axioms N11Formalization.C450Source16GroupedC17.valid5
#print axioms N11Formalization.C450Source16GroupedC17.valid6
#print axioms N11Formalization.C450Source16GroupedC17.valid7
#print axioms N11Formalization.C450Source16GroupedC17.valid8
#print axioms N11Formalization.C450Source16GroupedC17.valid9
#print axioms N11Formalization.C450Source16GroupedC17.valid10
#print axioms N11Formalization.C450Source16GroupedC17.valid11
#print axioms N11Formalization.C450Source16GroupedC17.bound
#print axioms N11Formalization.C450Source16GroupedC17.endpoint_checks
