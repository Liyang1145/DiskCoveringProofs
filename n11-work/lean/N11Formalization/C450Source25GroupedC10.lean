import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((3243030287:ℚ)/5000000000),((6799357827:ℚ)/10000000000),((-32875504789:ℚ)/99200000000),((-5889090861:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5482670683:ℚ)/10000000000),((775519817898475497266323865922698795990446747149344729321:ℚ)/3308060253906250000000000000000000000000000000000000000000),((3111186131523405465504779:ℚ)/92416000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6725754753:ℚ)/10000000000),((3459585131:ℚ)/5000000000),((-16857095917:ℚ)/51500000000),((-12497264259:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2421858099:ℚ)/5000000000),((5314693582435038409198448180561178494231746839903831936823:ℚ)/23221684931054687500000000000000000000000000000000000000000),((8117353211349947604823019:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6845541441:ℚ)/10000000000),((1407788881:ℚ)/2000000000),((-6910522167:ℚ)/20980000000),((-4285541441:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((561688947:ℚ)/1250000000),((2112670817951943364047216833654578391856371921808985239539:ℚ)/9243906012500000000000000000000000000000000000000000000000),((5934375473442627373630571:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((6965290777:ℚ)/10000000000),((44367611:ℚ)/62500000),((-72857759:ℚ)/222500000),((-13215872331:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2057953081:ℚ)/5000000000),((76798181800007466251744391288250278304155417315387104409:ℚ)/339775381040573120117187500000000000000000000000000000000),((3738507642805992098436539:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1405030413:ℚ)/2000000000),((7158682297:ℚ)/10000000000),((-35390776079:ℚ)/107750000000),((-2679091239:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((244647569:ℚ)/625000000),((781621484995807726960308781856925012815985774565796663099:ℚ)/3459759573706250000000000000000000000000000000000000000000),((105429293688135387250979:ℚ)/14786560000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((28340019:ℚ)/40000000),((7218538247:ℚ)/10000000000),((-35809767729:ℚ)/108700000000),((-1064707:ℚ)/4300000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3702484679:ℚ)/10000000000),((30493621018398290345232350433216620825590886511:ℚ)/135037670312500000000000000000000000000000000000),((24475609691295887651:ℚ)/5914624000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7144849059:ℚ)/10000000000),((7278385837:ℚ)/10000000000),((-36228700859:ℚ)/109650000000),((-1964935311:ℚ)/7900000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((434798027:ℚ)/1250000000),((7944521008802726799312677411373346800948088289817404919:ℚ)/35196436425781250000000000000000000000000000000000000000),((420484680999552050269571:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7204685213:ℚ)/10000000000),((3669112641:ℚ)/5000000000),((-18323788487:ℚ)/55300000000),((-13934055639:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1619759139:ℚ)/5000000000),((8456660483167027521132021109845625760265749838924703573133:ℚ)/37480372877337646484375000000000000000000000000000000000000),((-691993124126936482772221:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7264513421:ℚ)/10000000000),((924757099:ℚ)/1250000000),((-4633299693:ℚ)/13943750000),((-4704513421:ℚ)/18750000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((596467039:ℚ)/2000000000),((80979476277030825426682208106792028963950464838161294561:ℚ)/359040498733520507812500000000000000000000000000000000000),((-1807710328003219547426269:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((7324333889:ℚ)/10000000000),((1879424203:ℚ)/2500000000),((-9475969421:ℚ)/28125000000),((-14293001667:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((270160239:ℚ)/1000000000),((798487152476931126177973906390634980268139707216448991099:ℚ)/3509048400000000000000000000000000000000000000000000000000),((-2926669440267088255043989:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((1488790477:ℚ)/2000000000),((484805631:ℚ)/625000000),((-2473639417:ℚ)/7150000000),((-976790477:ℚ)/3940000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((507484393:ℚ)/2500000000),((3162116678960156265503785508200758070178874194343984849:ℚ)/13666104237500000000000000000000000000000000000000000000),((-206972913332260758957661:ℚ)/14786560000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((7683104743:ℚ)/10000000000),((7995976837:ℚ)/10000000000),((-41251837859:ℚ)/118200000000),((-15369314229:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((64530598068667058319733995422207342841143068501331723229923:ℚ)/279470356250000000000000000000000000000000000000000000000000),((-1407001:ℚ)/64000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((7922153157:ℚ)/10000000000),((4236934319:ℚ)/5000000000),((-22298540233:ℚ)/61000000000),((-5362153157:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((101485929995533017527306331215485592601379847981799577187:ℚ)/426902400000000000000000000000000000000000000000000000000),((-1407001:ℚ)/64000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((32812403:ℚ)/39062500),((10382670327:ℚ)/10000000000),((-57958692289:ℚ)/129600000000),((-68437209:ℚ)/312500000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1408652605961827170944439749349636162644862611830033:ℚ)/5149841308593750000000000000000000000000000000000000),((-1407001:ℚ)/64000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((1288570609:ℚ)/1250000000),((7096486769:ℚ)/5000000000),((-42315407383:ℚ)/80000000000),((-968570609:ℚ)/4600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((47858740711888863323767371251844104006847550140847299:ℚ)/152087500000000000000000000000000000000000000000000000),((-1407001:ℚ)/64000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC10
#check @N11Formalization.C450Source25GroupedC10.bound
#print axioms N11Formalization.C450Source25GroupedC10.valid0
#print axioms N11Formalization.C450Source25GroupedC10.valid1
#print axioms N11Formalization.C450Source25GroupedC10.valid2
#print axioms N11Formalization.C450Source25GroupedC10.valid3
#print axioms N11Formalization.C450Source25GroupedC10.valid4
#print axioms N11Formalization.C450Source25GroupedC10.valid5
#print axioms N11Formalization.C450Source25GroupedC10.valid6
#print axioms N11Formalization.C450Source25GroupedC10.valid7
#print axioms N11Formalization.C450Source25GroupedC10.valid8
#print axioms N11Formalization.C450Source25GroupedC10.valid9
#print axioms N11Formalization.C450Source25GroupedC10.valid10
#print axioms N11Formalization.C450Source25GroupedC10.valid11
#print axioms N11Formalization.C450Source25GroupedC10.valid12
#print axioms N11Formalization.C450Source25GroupedC10.valid13
#print axioms N11Formalization.C450Source25GroupedC10.valid14
#print axioms N11Formalization.C450Source25GroupedC10.bound
#print axioms N11Formalization.C450Source25GroupedC10.endpoint_checks
