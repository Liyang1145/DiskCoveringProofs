import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((6245054653:ℚ)/10000000000),((6522965079:ℚ)/10000000000),((-342222427:ℚ)/3200000000),((-1445054653:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((757972161:ℚ)/1250000000),((1810844367059988177247379268884641094357483159100959977:ℚ)/32013486328125000000000000000000000000000000000000000000),((-153181846977006128021697:ℚ)/5120000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((81043481:ℚ)/125000000),((3380715419:ℚ)/5000000000),((-5662146257:ℚ)/51500000000),((-21043481:ℚ)/667500000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5489185691:ℚ)/10000000000),((33503311828058080492398169051305015522679499434121:ℚ)/598302853088378906250000000000000000000000000000000),((-521944496226175563547:ℚ)/15200000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((672183621:ℚ)/1000000000),((860079781:ℚ)/1250000000),((-1460239343:ℚ)/13350000000),((-192183621:ℚ)/5435000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1213694291:ℚ)/2500000000),((61601396494896541097839879029793556996072182938387083:ℚ)/1116294236005859375000000000000000000000000000000000000),((-113121368747061129469321:ℚ)/2918400000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((684099247:ℚ)/1000000000),((1399965971:ℚ)/2000000000),((-2407897913:ℚ)/21740000000),((-204099247:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((901454259:ℚ)/2000000000),((37009660431439360654256813774952198257792774871716389:ℚ)/673187819088134765625000000000000000000000000000000000),((-39859540746918776740443:ℚ)/972800000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((3480067351:ℚ)/5000000000),((7059419987:ℚ)/10000000000),((-12218259961:ℚ)/110600000000),((-1080067351:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((826566253:ℚ)/2000000000),((3199017657823295780903397212825485209173385709987548929:ℚ)/58563082620840072631835937500000000000000000000000000000),((-1050317427004695824541227:ℚ)/24320000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((438731299:ℚ)/625000000),((1423801293:ℚ)/2000000000),((-2479403879:ℚ)/22310000000),((-138731299:ℚ)/3515625000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3933119097:ℚ)/10000000000),((4840354529677183175670617101052106294167075950434659:ℚ)/88752076408127322793006896972656250000000000000000000),((-885887256801602134033:ℚ)/20000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((3539631811:ℚ)/5000000000),((897323673:ℚ)/1250000000),((-1571971019:ℚ)/14062500000),((-1139631811:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1861652697:ℚ)/5000000000),((727981164649841656218088983023161418335749173526199:ℚ)/13368565874862670898437500000000000000000000000000000),((-1104165112843762265805267:ℚ)/24320000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((7138823301:ℚ)/10000000000),((7238168831:ℚ)/10000000000),((-12754506493:ℚ)/113450000000),((-2338823301:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3501570321:ℚ)/10000000000),((138762192098660895697191587369144562613086976076792965451:ℚ)/2551932955000000000000000000000000000000000000000000000000),((-13573153081798266024115081:ℚ)/291840000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((3599189949:ℚ)/5000000000),((7297744893:ℚ)/10000000000),((-12933234679:ℚ)/114400000000),((-399729983:ℚ)/9612500000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1632740803:ℚ)/5000000000),((63141365165880446858909623339409621039117135550769:ℚ)/1162830503350496292114257812500000000000000000000000),((-3474095610095941617481081:ℚ)/72960000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((725793349:ℚ)/1000000000),((1471463531:ℚ)/2000000000),((-2622390593:ℚ)/23070000000),((-245793349:ℚ)/5815000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3011660493:ℚ)/10000000000),((640600170306640984276341298224317115083548300604692923:ℚ)/11813144799248046875000000000000000000000000000000000000),((-47398899454607341943427:ℚ)/972800000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((914685519:ℚ)/1250000000),((3738226797:ℚ)/5000000000),((-6734680391:ℚ)/58150000000),((-104895173:ℚ)/2462500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((547033861:ℚ)/2000000000),((18422488365215790508164033769243521319425625608748977:ℚ)/339186431846618652343750000000000000000000000000000000),((-11959716830442789900139:ℚ)/240000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7436576967:ℚ)/10000000000),((7714689243:ℚ)/10000000000),((-14184067729:ℚ)/118200000000),((-2636576967:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((519381111:ℚ)/2500000000),((190339999350755173948833925658258331777528054063316568477:ℚ)/3493379453125000000000000000000000000000000000000000000000),((-15189884107754118966971809:ℚ)/291840000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7674730433:ℚ)/10000000000),((8191030577:ℚ)/10000000000),((-15613091731:ℚ)/122000000000),((-2874730433:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((23699984910416041013579052278356114874973914422041678353:ℚ)/432238680000000000000000000000000000000000000000000000000),((-1762941:ℚ)/32000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((326036879:ℚ)/400000000),((2523779427:ℚ)/2500000000),((-5331338281:ℚ)/32400000000),((-134036879:ℚ)/3200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3978094677754380412828409382764573835838444053917891:ℚ)/69120000000000000000000000000000000000000000000000000),((-1762941:ℚ)/32000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((10054553067:ℚ)/10000000000),((694995467:ℚ)/500000000),((-1636986401:ℚ)/8000000000),((-76152943:ℚ)/1600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((15315521908472530294111263459226733340718161383347:ℚ)/240000000000000000000000000000000000000000000000000),((-1762941:ℚ)/32000000)⟩
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
end N11Formalization.C450Source16GroupedC14
#check @N11Formalization.C450Source16GroupedC14.bound
#print axioms N11Formalization.C450Source16GroupedC14.valid0
#print axioms N11Formalization.C450Source16GroupedC14.valid1
#print axioms N11Formalization.C450Source16GroupedC14.valid2
#print axioms N11Formalization.C450Source16GroupedC14.valid3
#print axioms N11Formalization.C450Source16GroupedC14.valid4
#print axioms N11Formalization.C450Source16GroupedC14.valid5
#print axioms N11Formalization.C450Source16GroupedC14.valid6
#print axioms N11Formalization.C450Source16GroupedC14.valid7
#print axioms N11Formalization.C450Source16GroupedC14.valid8
#print axioms N11Formalization.C450Source16GroupedC14.valid9
#print axioms N11Formalization.C450Source16GroupedC14.valid10
#print axioms N11Formalization.C450Source16GroupedC14.valid11
#print axioms N11Formalization.C450Source16GroupedC14.valid12
#print axioms N11Formalization.C450Source16GroupedC14.valid13
#print axioms N11Formalization.C450Source16GroupedC14.valid14
#print axioms N11Formalization.C450Source16GroupedC14.bound
#print axioms N11Formalization.C450Source16GroupedC14.endpoint_checks
