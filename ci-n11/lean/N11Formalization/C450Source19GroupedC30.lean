import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((86878029:ℚ)/156250000),((3055359269:ℚ)/5000000000),((1299414377:ℚ)/1668750000),((24267514883:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((93765479:ℚ)/125000000),((-31436557817094496236564920095325441:ℚ)/371760996093750000000000000000000000),((-649586391651838095996121057:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6035892661:ℚ)/10000000000),((1269724801:ℚ)/2000000000),((89346604593:ℚ)/110600000000),((10040073607:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3265561679:ℚ)/5000000000),((-828343409750418510913546685269662730049160379678894625499:ℚ)/8455618850000000000000000000000000000000000000000000000000),((-102788568263401191528052937:ℚ)/295731200000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6273705977:ℚ)/10000000000),((6586502471:ℚ)/10000000000),((92438177701:ℚ)/114400000000),((51865517297:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2998653631:ℚ)/5000000000),((-917971963592641085017482984574907625586762219002174074583:ℚ)/9357462400000000000000000000000000000000000000000000000000),((-2541012651019274378576301817:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((162787461:ℚ)/250000000),((6705432409:ℚ)/10000000000),((2388236993:ℚ)/2907500000),((52698026863:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2709055627:ℚ)/5000000000),((-11998306223894732012652372048908947182921917191440977:ℚ)/115212725610351562500000000000000000000000000000000000),((-2526635457276409887161175097:ℚ)/7393280000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6630387491:ℚ)/10000000000),((1706089137:ℚ)/2500000000),((97075037383:ℚ)/118200000000),((13382623959:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5106655529:ℚ)/10000000000),((-805582756140509557893051379121061595406977276221299732983:ℚ)/7740940162500000000000000000000000000000000000000000000000),((-471045114103943412879163259:ℚ)/1386240000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1349854413:ℚ)/2000000000),((6943275167:ℚ)/10000000000),((19724107369:ℚ)/24020000000),((54362926169:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4776838039:ℚ)/10000000000),((-27023879822735296522471229045859053732988891761881240609:ℚ)/259848540150000000000000000000000000000000000000000000000),((-2497828073702922951731117193:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((3434076187:ℚ)/5000000000),((3531094261:ℚ)/5000000000),((50082990431:ℚ)/61000000000),((27597659827:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4424526569:ℚ)/10000000000),((-147442021232796061902970662159535990755818445032235062157:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-620849456048087210979378177:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((3493514309:ℚ)/5000000000),((7181096857:ℚ)/10000000000),((16951895339:ℚ)/20650000000),((56027677999:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((4043816303:ℚ)/10000000000),((-1429121107928379749003200334973330752694353367595250673:ℚ)/13758788476562500000000000000000000000000000000000000000),((-2468949832793748389627849913:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((7105900983:ℚ)/10000000000),((18250001:ℚ)/25000000),((2790721967:ℚ)/3400000000),((142150007:ℚ)/154875000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1812869987:ℚ)/5000000000),((-24903185632526339125230974133388729112873528559509:ℚ)/239892578125000000000000000000000000000000000000000),((-15340525462970574517737:ℚ)/46208000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((7224769647:ℚ)/10000000000),((1884448489:ℚ)/2500000000),((104802005411:ℚ)/129600000000),((14631139423:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1577721821:ℚ)/5000000000),((-49638308151454088418667917420851181201775836585436135459:ℚ)/503884800000000000000000000000000000000000000000000000000),((-151593697518896311059417177:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((3731248261:ℚ)/5000000000),((8488813859:ℚ)/10000000000),((53946227393:ℚ)/72400000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((952559303:ℚ)/5000000000),((-32407421067746573535813845592814637262151241357724598793:ℚ)/444730575000000000000000000000000000000000000000000000000),((-167444923:ℚ)/512000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((8413284799:ℚ)/10000000000),((4719819863:ℚ)/5000000000),((120252702387:ℚ)/160000000000),((35918739041:ℚ)/36200000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-483530812136742091979964005347815095665806107991094348089:ℚ)/6400000000000000000000000000000000000000000000000000000000),((-167444923:ℚ)/512000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((9363923151:ℚ)/10000000000),((13241805213:ℚ)/10000000000),((132611000963:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-50087148609166363731693722463624000283:ℚ)/2691145728000000000000000000000000000000),((-167444923:ℚ)/512000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source19 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC30
#check @N11Formalization.C450Source19GroupedC30.bound
#print axioms N11Formalization.C450Source19GroupedC30.valid0
#print axioms N11Formalization.C450Source19GroupedC30.valid1
#print axioms N11Formalization.C450Source19GroupedC30.valid2
#print axioms N11Formalization.C450Source19GroupedC30.valid3
#print axioms N11Formalization.C450Source19GroupedC30.valid4
#print axioms N11Formalization.C450Source19GroupedC30.valid5
#print axioms N11Formalization.C450Source19GroupedC30.valid6
#print axioms N11Formalization.C450Source19GroupedC30.valid7
#print axioms N11Formalization.C450Source19GroupedC30.valid8
#print axioms N11Formalization.C450Source19GroupedC30.valid9
#print axioms N11Formalization.C450Source19GroupedC30.valid10
#print axioms N11Formalization.C450Source19GroupedC30.valid11
#print axioms N11Formalization.C450Source19GroupedC30.valid12
#print axioms N11Formalization.C450Source19GroupedC30.bound
#print axioms N11Formalization.C450Source19GroupedC30.endpoint_checks
