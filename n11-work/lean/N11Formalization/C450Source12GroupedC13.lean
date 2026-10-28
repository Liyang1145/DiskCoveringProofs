import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((1565634469:ℚ)/2500000000),((3266693723:ℚ)/5000000000),((-2466693723:ℚ)/12400000000),((-2936903407:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3011646623:ℚ)/5000000000),((7130593304483446311987836077965955026582017575146536559:ℚ)/206753765869140625000000000000000000000000000000000000000),((290630445684953705790733:ℚ)/11552000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6500498519:ℚ)/10000000000),((6771390623:ℚ)/10000000000),((-5171390623:ℚ)/25750000000),((-12461495557:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((544611267:ℚ)/1000000000),((46572147203969199099699899670069654942667259077579433053:ℚ)/1361471381250000000000000000000000000000000000000000000000),((1066076503620296256560533:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6738426293:ℚ)/10000000000),((6890378979:ℚ)/10000000000),((-5290378979:ℚ)/26700000000),((-13175278879:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2403893803:ℚ)/5000000000),((4504844242245758800723156852855850776697589259667631475619:ℚ)/133955308320703125000000000000000000000000000000000000000000),((2905188560457794715414071:ℚ)/138624000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((857172367:ℚ)/1250000000),((7009359121:ℚ)/10000000000),((-5409359121:ℚ)/27175000000),((-1691517101:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((445752009:ℚ)/1000000000),((587808381948238904219173286626744210631492269613340789:ℚ)/17530932788753509521484375000000000000000000000000000000),((920242194801885168336757:ℚ)/46208000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((6976324599:ℚ)/10000000000),((1767211561:ℚ)/2500000000),((-1367211561:ℚ)/6912500000),((-13888973797:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4079464639:ℚ)/10000000000),((623579080560033942035416533580969363172135680305686806323:ℚ)/18740186438668823242187500000000000000000000000000000000000),((54464350938860067462917:ℚ)/2888000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((1758948731:ℚ)/2500000000),((1782082867:ℚ)/2500000000),((-1382082867:ℚ)/6971875000),((-3516846193:ℚ)/28125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((969372699:ℚ)/2500000000),((838987528215997833238018761248293649230303365594527467:ℚ)/25245035067200660705566406250000000000000000000000000000),((52960587306126922794653:ℚ)/2888000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((7095263637:ℚ)/10000000000),((7187814841:ℚ)/10000000000),((-1862604947:ℚ)/9375000000),((-14245790911:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((73299981:ℚ)/200000000),((142003364275672461634862110914619366534864902730101731:ℚ)/4277941079956054687500000000000000000000000000000000000),((823315562652755809396037:ℚ)/46208000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((894341347:ℚ)/1250000000),((7247296409:ℚ)/10000000000),((-5647296409:ℚ)/28362500000),((-138694157:ℚ)/1100000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1720018303:ℚ)/5000000000),((39114929907514592789655457352261512842967820312100271:ℚ)/1179702734375000000000000000000000000000000000000000000),((799268096479766927276037:ℚ)/46208000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((7214196381:ℚ)/10000000000),((3653388109:ℚ)/5000000000),((-19953763:ℚ)/100000000),((-14602589143:ℚ)/115350000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3199969871:ℚ)/10000000000),((258552640999520292114187914522338046255957190616483:ℚ)/7806414567947387695312500000000000000000000000000000),((193806745439620866862237:ℚ)/11552000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((727366049:ℚ)/1000000000),((7366254309:ℚ)/10000000000),((-5766254309:ℚ)/28837500000),((-1478098147:ℚ)/11630000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2941097623:ℚ)/10000000000),((46902095882957970023070053084387862980389015866211726847:ℚ)/1417577375909765625000000000000000000000000000000000000000),((2253576607975652855046311:ℚ)/138624000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7333123141:ℚ)/10000000000),((1871301377:ℚ)/2500000000),((-1471301377:ℚ)/7268750000),((-14959369423:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1328962709:ℚ)/5000000000),((230663334717153076678125038630635859909872990166699055769:ℚ)/6946538124218750000000000000000000000000000000000000000000),((45492647937633444396533:ℚ)/2888000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((3726022103:ℚ)/5000000000),((386154453:ℚ)/500000000),((-306154453:ℚ)/1477500000),((-7658066309:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((395285861:ℚ)/2000000000),((28721318612790269712799848775138733515725039147633229417:ℚ)/859027734375000000000000000000000000000000000000000000000),((447239897115869:ℚ)/30400000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((3844935159:ℚ)/5000000000),((409939427:ℚ)/500000000),((-329939427:ℚ)/1525000000),((-8014805477:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((8130806564414701700107190846144962233789123261545708557:ℚ)/240132600000000000000000000000000000000000000000000000000),((214073:ℚ)/16000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((1020683133:ℚ)/1250000000),((10100920881:ℚ)/10000000000),((-8500920881:ℚ)/32400000000),((-2182049399:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((9224639213015400465917109247369674316428143303487895417:ℚ)/253125000000000000000000000000000000000000000000000000000),((214073:ℚ)/16000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((5033639133:ℚ)/5000000000),((3475855587:ℚ)/2500000000),((-3075855587:ℚ)/10000000000),((-11580917399:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1780640965322359237205044933682791627819554550164804139:ℚ)/43801200000000000000000000000000000000000000000000000000),((214073:ℚ)/16000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC13
#check @N11Formalization.C450Source12GroupedC13.bound
#print axioms N11Formalization.C450Source12GroupedC13.valid0
#print axioms N11Formalization.C450Source12GroupedC13.valid1
#print axioms N11Formalization.C450Source12GroupedC13.valid2
#print axioms N11Formalization.C450Source12GroupedC13.valid3
#print axioms N11Formalization.C450Source12GroupedC13.valid4
#print axioms N11Formalization.C450Source12GroupedC13.valid5
#print axioms N11Formalization.C450Source12GroupedC13.valid6
#print axioms N11Formalization.C450Source12GroupedC13.valid7
#print axioms N11Formalization.C450Source12GroupedC13.valid8
#print axioms N11Formalization.C450Source12GroupedC13.valid9
#print axioms N11Formalization.C450Source12GroupedC13.valid10
#print axioms N11Formalization.C450Source12GroupedC13.valid11
#print axioms N11Formalization.C450Source12GroupedC13.valid12
#print axioms N11Formalization.C450Source12GroupedC13.valid13
#print axioms N11Formalization.C450Source12GroupedC13.valid14
#print axioms N11Formalization.C450Source12GroupedC13.bound
#print axioms N11Formalization.C450Source12GroupedC13.endpoint_checks
