import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/8),((3:ℚ)/16),((2945807269:ℚ)/5000000000),((3106347479:ℚ)/5000000000),((7265807269:ℚ)/25750000000),((18279042437:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6837450041:ℚ)/10000000000),((-29063956930527832726690374552447832373957136210188016907:ℚ)/320134863281250000000000000000000000000000000000000000000),((-1143124829943949611529207931:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((6132799557:ℚ)/10000000000),((806679131:ℚ)/1250000000),((4924266519:ℚ)/17800000000),((4660037393:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6318312039:ℚ)/10000000000),((-773597458179463712309369777599758148257367110484064939:ℚ)/8812112500000000000000000000000000000000000000000000000),((-72854786499172013404818451:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6373716653:ℚ)/10000000000),((6573715533:ℚ)/10000000000),((15013716653:ℚ)/54350000000),((37641146599:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5760020567:ℚ)/10000000000),((-88173572080857690226040162368654371380992171462927333817:ℚ)/1003410549218750000000000000000000000000000000000000000000),((-4782670704944881427020503299:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((3247041879:ℚ)/5000000000),((836743047:ℚ)/1250000000),((7567041879:ℚ)/27650000000),((4750229141:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5462382487:ℚ)/10000000000),((-178520925690044194533218272181668766535268553873086011:ℚ)/2064360070800781250000000000000000000000000000000000000),((-75409501888295994454480219:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6614394201:ℚ)/10000000000),((3407061181:ℚ)/5000000000),((1694932689:ℚ)/6250000000),((19181183543:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((257477357:ℚ)/500000000),((-507444908621553542015942177722772801637726583469069:ℚ)/5960464477539062500000000000000000000000000000000000),((-1217285052118286076284662051:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((6734650929:ℚ)/10000000000),((1386850417:ℚ)/2000000000),((1397695539:ℚ)/5200000000),((7744551251:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((963703599:ℚ)/2000000000),((-73681227768239486392787133248439672811935988178248799:ℚ)/878800000000000000000000000000000000000000000000000000),((-196458753452040848853925099:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1713714171:ℚ)/2500000000),((1763583991:ℚ)/2500000000),((3873714171:ℚ)/14537500000),((9770751973:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((69768931:ℚ)/156250000),((-1586058195471639210075298115268051816721923192855762999:ℚ)/19202120935058593750000000000000000000000000000000000000),((-309574733940656061780490171:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((871876753:ℚ)/1250000000),((3587188129:ℚ)/5000000000),((1951876753:ℚ)/7387500000),((19721564387:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((510476143:ℚ)/1250000000),((-5697453894146918803977114644336978272102703143703053:ℚ)/69995480346679687500000000000000000000000000000000000),((-1248580637705837053780101131:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7095125339:ℚ)/10000000000),((741433441:ℚ)/1000000000),((15735125339:ℚ)/61000000000),((4016300323:ℚ)/11820000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3665506819:ℚ)/10000000000),((-331509956538662242870041080700199040951699956435989292877:ℚ)/4255893750000000000000000000000000000000000000000000000000),((-49992281634645234997138571:ℚ)/147865600000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((3667609341:ℚ)/5000000000),((7893812181:ℚ)/10000000000),((98612461:ℚ)/400000000),((681990763:ℚ)/2000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((82731503:ℚ)/312500000),((-28656434668515696066317711196233591094581686743881:ℚ)/400000000000000000000000000000000000000000000000000),((-10472921837949697:ℚ)/30400000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((1562988473:ℚ)/2000000000),((9807425511:ℚ)/10000000000),((3290988473:ℚ)/16000000000),((47342276533:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-3843252369713191700209949236112914082365764306776978831:ℚ)/76800000000000000000000000000000000000000000000000000000),((-582897:ℚ)/1638400)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((4864650389:ℚ)/5000000000),((6811668283:ℚ)/5000000000),((9184650389:ℚ)/55200000000),((29395004849:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-20244585667662138034304410989541590175831278419124284627:ℚ)/788421600000000000000000000000000000000000000000000000000),((-582897:ℚ)/1638400)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC19
#check @N11Formalization.C450Source29GroupedC19.bound
#print axioms N11Formalization.C450Source29GroupedC19.valid0
#print axioms N11Formalization.C450Source29GroupedC19.valid1
#print axioms N11Formalization.C450Source29GroupedC19.valid2
#print axioms N11Formalization.C450Source29GroupedC19.valid3
#print axioms N11Formalization.C450Source29GroupedC19.valid4
#print axioms N11Formalization.C450Source29GroupedC19.valid5
#print axioms N11Formalization.C450Source29GroupedC19.valid6
#print axioms N11Formalization.C450Source29GroupedC19.valid7
#print axioms N11Formalization.C450Source29GroupedC19.valid8
#print axioms N11Formalization.C450Source29GroupedC19.valid9
#print axioms N11Formalization.C450Source29GroupedC19.valid10
#print axioms N11Formalization.C450Source29GroupedC19.valid11
#print axioms N11Formalization.C450Source29GroupedC19.bound
#print axioms N11Formalization.C450Source29GroupedC19.endpoint_checks
