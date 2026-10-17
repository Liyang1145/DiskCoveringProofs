import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((1113329919:ℚ)/2000000000),((1529497391:ℚ)/2500000000),((1305329919:ℚ)/1780000000),((22923466083:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1872192477:ℚ)/2500000000),((-12038981415747632305041036090032551:ℚ)/176242250000000000000000000000000000),((-5405002191589856472283907:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((1208556023:ℚ)/2000000000),((3178037713:ℚ)/5000000000),((4201668069:ℚ)/5530000000),((15798163423:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6516195149:ℚ)/10000000000),((-42546963129871247874489327548753645105677209222887139:ℚ)/528476178125000000000000000000000000000000000000000000),((-21441107145139695458846843:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((6280786923:ℚ)/10000000000),((6594122233:ℚ)/10000000000),((21722360769:ℚ)/28600000000),((97883589029:ℚ)/110600000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2990390007:ℚ)/5000000000),((-5899870393836548417890945970822342589437078068320841591:ℚ)/73105175000000000000000000000000000000000000000000000000),((-85042767677562069980345083:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((162968999:ℚ)/250000000),((209785381:ℚ)/312500000),((560906997:ℚ)/726875000),((3107209953:ℚ)/3575000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((674944341:ℚ)/1250000000),((-25846159428696647443600378961135177026705900331603:ℚ)/300033139610290527343750000000000000000000000000000),((-20673746117197277888423:ℚ)/56406250000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6637734853:ℚ)/10000000000),((854016721:ℚ)/1250000000),((7597734853:ℚ)/9850000000),((12622217373:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((254342029:ℚ)/500000000),((-192840639883148989553840501504084773819142971268948329:ℚ)/2239855371093750000000000000000000000000000000000000000),((-1317422559036082089294527:ℚ)/3610000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6756702497:ℚ)/10000000000),((3475563679:ℚ)/5000000000),((23150107491:ℚ)/30025000000),((17087442609:ℚ)/19700000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2377763639:ℚ)/5000000000),((-7278090466431809938365658906949592092521679811737532621:ℚ)/84586113330078125000000000000000000000000000000000000000),((-20987226456544186697722427:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((1718915809:ℚ)/2500000000),((7070113339:ℚ)/10000000000),((5876747427:ℚ)/7625000000),((104071473407:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2200694037:ℚ)/5000000000),((-119128619297333455383452801977479654906936517528481373:ℚ)/1385382080078125000000000000000000000000000000000000000),((-83581249382776837230564787:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6994617393:ℚ)/10000000000),((3594546031:ℚ)/5000000000),((7954617393:ℚ)/10325000000),((52809098403:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((4018361949:ℚ)/10000000000),((-73896459134947185146903951710890815904123533205868207:ℚ)/859924279785156250000000000000000000000000000000000000),((-20803018413131573741464667:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3556782637:ℚ)/5000000000),((456753991:ℚ)/625000000),((12110347911:ℚ)/15725000000),((6697801883:ℚ)/7743750000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3597199803:ℚ)/10000000000),((-1019040266410852969087160547749993976046684917276249:ℚ)/11866483163833618164062500000000000000000000000000000),((-323599132384072447549057:ℚ)/902500000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((7232507163:ℚ)/10000000000),((7545987883:ℚ)/10000000000),((2730835721:ℚ)/3600000000),((110257842479:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((156123533:ℚ)/500000000),((-1314399673553136234817236891618398212495633952433511:ℚ)/16200000000000000000000000000000000000000000000000000),((-227411145395154871739803:ℚ)/640000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((7470374023:ℚ)/10000000000),((1889730713:ℚ)/2000000000),((25291122069:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1849581369:ℚ)/10000000000),((-441608110391795278814053358048105431363210386507573291:ℚ)/12500000000000000000000000000000000000000000000000000000),((-9077587:ℚ)/25600000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((9372680489:ℚ)/10000000000),((13251780163:ℚ)/10000000000),((10332680489:ℚ)/18400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-5747162891204333904070273297577173:ℚ)/778688000000000000000000000000000000),((-9077587:ℚ)/25600000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC29
#check @N11Formalization.C450Source20GroupedC29.bound
#print axioms N11Formalization.C450Source20GroupedC29.valid0
#print axioms N11Formalization.C450Source20GroupedC29.valid1
#print axioms N11Formalization.C450Source20GroupedC29.valid2
#print axioms N11Formalization.C450Source20GroupedC29.valid3
#print axioms N11Formalization.C450Source20GroupedC29.valid4
#print axioms N11Formalization.C450Source20GroupedC29.valid5
#print axioms N11Formalization.C450Source20GroupedC29.valid6
#print axioms N11Formalization.C450Source20GroupedC29.valid7
#print axioms N11Formalization.C450Source20GroupedC29.valid8
#print axioms N11Formalization.C450Source20GroupedC29.valid9
#print axioms N11Formalization.C450Source20GroupedC29.valid10
#print axioms N11Formalization.C450Source20GroupedC29.valid11
#print axioms N11Formalization.C450Source20GroupedC29.bound
#print axioms N11Formalization.C450Source20GroupedC29.endpoint_checks
