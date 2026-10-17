import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((784005823:ℚ)/1250000000),((6547780479:ℚ)/10000000000),((-4627780479:ℚ)/24800000000),((-1312017469:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((750146823:ℚ)/1250000000),((57232552318393997397195914143835586918403368762537255703:ℚ)/1240522595214843750000000000000000000000000000000000000000),((3771571088008136112915969:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6510210761:ℚ)/10000000000),((848248019:ℚ)/1250000000),((-608248019:ℚ)/3218750000),((-11210632283:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((677674487:ℚ)/1250000000),((8968870443421553392499586780801251157062413073959996088579:ℚ)/196051878900000000000000000000000000000000000000000000000000),((196358589806779771174022481:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((674832749:ℚ)/1000000000),((6905067461:ℚ)/10000000000),((-4985067461:ℚ)/26700000000),((-1192498247:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((149360651:ℚ)/312500000),((32131712771407642113222008541468403788311920118589956833:ℚ)/714428311043750000000000000000000000000000000000000000000),((1513324620789004014301161:ℚ)/147865600000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((54938957:ℚ)/80000000),((7024139271:ℚ)/10000000000),((-5104139271:ℚ)/27175000000),((-98256871:ℚ)/884800000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((221346573:ℚ)/500000000),((9890736229713654543279553753473903583204006306368061:ℚ)/220590184558800000000000000000000000000000000000000000),((8244322686273648619689:ℚ)/946339840000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((3493200843:ℚ)/5000000000),((885458881:ℚ)/1250000000),((-645458881:ℚ)/3456250000),((-6319602529:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1011478099:ℚ)/2500000000),((1667785106854387284516143483229553423412209413373638904567:ℚ)/37480372877337646484375000000000000000000000000000000000000),((26575311126090094446330489:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7045914101:ℚ)/10000000000),((892900021:ℚ)/1250000000),((-652900021:ℚ)/3485937500),((-12817742303:ℚ)/112500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3842123333:ℚ)/10000000000),((10339459423890402418635570762463464756308014970040740060749:ℚ)/232658243179321289062500000000000000000000000000000000000000),((95042548823485419141434361:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((7105424187:ℚ)/10000000000),((7202726697:ℚ)/10000000000),((-586969633:ℚ)/3125000000),((-12996272561:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1813754183:ℚ)/5000000000),((1012697464751456772613021751114535205081756425848724631:ℚ)/22815685759765625000000000000000000000000000000000000000),((83783473256006301469962009:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((1791233001:ℚ)/2500000000),((7262250699:ℚ)/10000000000),((-5342250699:ℚ)/28362500000),((-3293699003:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((340001363:ℚ)/1000000000),((14707829316490188734084971609935387434794194261306153143057:ℚ)/331751284150000000000000000000000000000000000000000000000000),((4532750409077990049910161:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((7224437607:ℚ)/10000000000),((3660886119:ℚ)/5000000000),((-2700886119:ℚ)/14300000000),((-13353312821:ℚ)/115350000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((78921279:ℚ)/250000000),((7118659611822937947559430562552083117615789663040412999:ℚ)/160749688783172607421875000000000000000000000000000000000),((61264138377375194749634289:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((1820985263:ℚ)/2500000000),((59050331:ℚ)/80000000),((-43690331:ℚ)/230700000),((-3382955789:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((578813863:ℚ)/2000000000),((5225736125837823949461932944925576997669790320968536527491:ℚ)/118131447992480468750000000000000000000000000000000000000000),((3125241140392047788242209:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7343442391:ℚ)/10000000000),((468770167:ℚ)/625000000),((-348770167:ℚ)/1817187500),((-13710327173:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((325716699:ℚ)/1250000000),((4933820867419340709984422317775942631036720567778514784707:ℚ)/111144609987500000000000000000000000000000000000000000000000),((38743156399766182425101841:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((93280487:ℚ)/125000000),((7738358893:ℚ)/10000000000),((-5818358893:ℚ)/29550000000),((-175841461:ℚ)/1525000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1905518537:ℚ)/10000000000),((585418479569301282289204233840100055786052915226242029:ℚ)/13100172949218750000000000000000000000000000000000000000),((2534445054407096500209:ℚ)/2310400000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((1925102247:ℚ)/2500000000),((821433671:ℚ)/1000000000),((-629433671:ℚ)/3050000000),((-3695306741:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((195545596302645231156292738237122178474646772925130016893:ℚ)/4322386800000000000000000000000000000000000000000000000000),((-680061:ℚ)/1024000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((2044066533:ℚ)/2500000000),((63233231:ℚ)/62500000),((-51233231:ℚ)/202500000),((-4052199599:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((525229189388268281566519345641531935617229851950349972867:ℚ)/10800000000000000000000000000000000000000000000000000000000),((-680061:ℚ)/1024000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10078878813:ℚ)/10000000000),((13920812161:ℚ)/10000000000),((-12000812161:ℚ)/40000000000),((-21916636439:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2740365808541240479363855188914729932294090785140525425643:ℚ)/50458982400000000000000000000000000000000000000000000000000),((-680061:ℚ)/1024000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC13
#check @N11Formalization.C450Source14GroupedC13.bound
#print axioms N11Formalization.C450Source14GroupedC13.valid0
#print axioms N11Formalization.C450Source14GroupedC13.valid1
#print axioms N11Formalization.C450Source14GroupedC13.valid2
#print axioms N11Formalization.C450Source14GroupedC13.valid3
#print axioms N11Formalization.C450Source14GroupedC13.valid4
#print axioms N11Formalization.C450Source14GroupedC13.valid5
#print axioms N11Formalization.C450Source14GroupedC13.valid6
#print axioms N11Formalization.C450Source14GroupedC13.valid7
#print axioms N11Formalization.C450Source14GroupedC13.valid8
#print axioms N11Formalization.C450Source14GroupedC13.valid9
#print axioms N11Formalization.C450Source14GroupedC13.valid10
#print axioms N11Formalization.C450Source14GroupedC13.valid11
#print axioms N11Formalization.C450Source14GroupedC13.valid12
#print axioms N11Formalization.C450Source14GroupedC13.valid13
#print axioms N11Formalization.C450Source14GroupedC13.valid14
#print axioms N11Formalization.C450Source14GroupedC13.bound
#print axioms N11Formalization.C450Source14GroupedC13.endpoint_checks
