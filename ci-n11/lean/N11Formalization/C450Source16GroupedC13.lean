import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((314027529:ℚ)/500000000),((6561232821:ℚ)/10000000000),((-4321232821:ℚ)/24800000000),((-462082587:ℚ)/5150000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((747666537:ℚ)/1250000000),((19273929109348400050450861066222906435215618372702731:ℚ)/330806025390625000000000000000000000000000000000000000),((7106844378304761074631:ℚ)/1945600000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6518955973:ℚ)/10000000000),((6799671047:ℚ)/10000000000),((-4559671047:ℚ)/25750000000),((-3318955973:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1349763257:ℚ)/2500000000),((5241829072444992872792979704663380697183934047352758077:ℚ)/90764758750000000000000000000000000000000000000000000000),((-439284172331578181933761:ℚ)/778240000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6757296593:ℚ)/10000000000),((3459432711:ℚ)/5000000000),((-2339432711:ℚ)/13350000000),((-10671889779:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4753819581:ℚ)/10000000000),((507013193516594530330140950525818093725321912093491397517:ℚ)/8930353888046875000000000000000000000000000000000000000000),((-3725051437271435756748041:ℚ)/778240000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((429777797:ℚ)/625000000),((3519022223:ℚ)/5000000000),((-2399022223:ℚ)/13587500000),((-689333391:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4398973949:ℚ)/10000000000),((24802793098081097341451970724845005700788550248148951:ℚ)/438273319718837738037109375000000000000000000000000000),((-20974093435853414486081:ℚ)/3040000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((1748894791:ℚ)/2500000000),((221800889:ℚ)/312500000),((-151800889:ℚ)/864062500),((-2846684373:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((160605003:ℚ)/400000000),((3289015299938776202269408527548811894332378653433896043:ℚ)/58563082620840072631835937500000000000000000000000000000),((-438415822297672776587929:ℚ)/48640000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((1763785359:ℚ)/2500000000),((3578604451:ℚ)/5000000000),((-2458604451:ℚ)/13943750000),((-963785359:ℚ)/9375000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((59525017:ℚ)/156250000),((94393585322272175550817643040434654799589551457278989:ℚ)/1683002337813377380371093750000000000000000000000000000),((-489853874317246167174729:ℚ)/48640000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((7114700531:ℚ)/10000000000),((3608392949:ℚ)/5000000000),((-2488392949:ℚ)/14062500000),((-11744101593:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3592953919:ℚ)/10000000000),((47925137551540701867401217184950827642934156665473853:ℚ)/855588215991210937500000000000000000000000000000000000),((-8660916452904872929146449:ℚ)/778240000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((448391033:ℚ)/625000000),((3638179761:ℚ)/5000000000),((-2518179761:ℚ)/14181250000),((-67743009:ℚ)/650000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1681514997:ℚ)/5000000000),((209500437435089817969032224495476134447483797420679:ℚ)/3744736328125000000000000000000000000000000000000000),((-37048506228400402495001:ℚ)/3040000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((1446761901:ℚ)/2000000000),((3667964929:ℚ)/5000000000),((-2547964929:ℚ)/14300000000),((-806761901:ℚ)/7690000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3116887641:ℚ)/10000000000),((33268927942867995932054587959860984826967157287087:ℚ)/595369217715454101562500000000000000000000000000000),((-412326657907901925285009:ℚ)/31129600000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((3646679769:ℚ)/5000000000),((1848874247:ℚ)/2500000000),((-429624749:ℚ)/2403125000),((-6140039307:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1425161501:ℚ)/5000000000),((659370722707502060073959006246649833684333037851740264661:ℚ)/11813144799248046875000000000000000000000000000000000000000),((-2783041005087629554169049:ℚ)/194560000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((73529067:ℚ)/100000000),((3757310969:ℚ)/5000000000),((-2637310969:ℚ)/14537500000),((-41529067:ℚ)/394000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((25569511:ℚ)/100000000),((77806126109265212063189466645830508675262973871903:ℚ)/1389307624843750000000000000000000000000000000000000),((-1195641128014056965601:ℚ)/77824000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((1867998171:ℚ)/2500000000),((1938209161:ℚ)/2500000000),((-1378209161:ℚ)/7387500000),((-3203994513:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((459491063:ℚ)/2500000000),((24612410262421652638707302551426320171537679678961565563:ℚ)/436672431640625000000000000000000000000000000000000000000),((-850353654740939019939969:ℚ)/48640000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((1927533283:ℚ)/2500000000),((257160619:ℚ)/312500000),((-187160619:ℚ)/953125000),((-1127533283:ℚ)/10800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((114135324529724392269170200901359244023928265355711403:ℚ)/2001105000000000000000000000000000000000000000000000000),((-20236513:ℚ)/1024000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((1637260189:ℚ)/2000000000),((506655537:ℚ)/500000000),((-394655537:ℚ)/1620000000),((-2991780567:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4232090580964905029383493391224986934486653679945796347:ℚ)/69120000000000000000000000000000000000000000000000000000),((-20236513:ℚ)/1024000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((5044929893:ℚ)/5000000000),((13937766319:ℚ)/10000000000),((-11697766319:ℚ)/40000000000),((-3444929893:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((199822626107175706445761377299329985217238813030175497:ℚ)/2920080000000000000000000000000000000000000000000000000),((-20236513:ℚ)/1024000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC13
#check @N11Formalization.C450Source16GroupedC13.bound
#print axioms N11Formalization.C450Source16GroupedC13.valid0
#print axioms N11Formalization.C450Source16GroupedC13.valid1
#print axioms N11Formalization.C450Source16GroupedC13.valid2
#print axioms N11Formalization.C450Source16GroupedC13.valid3
#print axioms N11Formalization.C450Source16GroupedC13.valid4
#print axioms N11Formalization.C450Source16GroupedC13.valid5
#print axioms N11Formalization.C450Source16GroupedC13.valid6
#print axioms N11Formalization.C450Source16GroupedC13.valid7
#print axioms N11Formalization.C450Source16GroupedC13.valid8
#print axioms N11Formalization.C450Source16GroupedC13.valid9
#print axioms N11Formalization.C450Source16GroupedC13.valid10
#print axioms N11Formalization.C450Source16GroupedC13.valid11
#print axioms N11Formalization.C450Source16GroupedC13.valid12
#print axioms N11Formalization.C450Source16GroupedC13.valid13
#print axioms N11Formalization.C450Source16GroupedC13.valid14
#print axioms N11Formalization.C450Source16GroupedC13.bound
#print axioms N11Formalization.C450Source16GroupedC13.endpoint_checks
