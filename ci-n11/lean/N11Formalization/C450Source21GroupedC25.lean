import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((2857308387:ℚ)/5000000000),((1252494261:ℚ)/2000000000),((3617308387:ℚ)/6675000000),((13832448349:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7198217393:ℚ)/10000000000),((-30317991583282742564540529991049:ℚ)/8261355468750000000000000000000000),((-629757332860939847811481:ℚ)/1732800000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6192147617:ℚ)/10000000000),((162527353:ℚ)/250000000),((7712147617:ℚ)/13825000000),((1782746177:ℚ)/2670000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1546219077:ℚ)/2500000000),((-222277469846192570536885598233889790958603943304706593:ℚ)/16514880566406250000000000000000000000000000000000000000),((-6647382508991300019741:ℚ)/18050000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((6430781657:ℚ)/10000000000),((6739641847:ℚ)/10000000000),((611598589:ℚ)/1100000000),((73456776623:ℚ)/110600000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5620667353:ℚ)/10000000000),((-117601270392218193545982397637640059084777926683021:ℚ)/8318750000000000000000000000000000000000000000000000),((-5339846341051533984560283:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1333867971:ℚ)/2000000000),((6858889873:ℚ)/10000000000),((1637867971:ℚ)/2907500000),((74530008857:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((500078931:ℚ)/1000000000),((-698029349378666636832167614616113920423499145694411:ℚ)/38404241870117187500000000000000000000000000000000000),((-5373984837327746048446923:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((1357718571:ℚ)/2000000000),((6978121791:ℚ)/10000000000),((1661718571:ℚ)/2955000000),((75603096119:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4663043573:ℚ)/10000000000),((-738076092824862683329099452696482384985564376683059:ℚ)/40317396679687500000000000000000000000000000000000000),((-16153145558130414469832641:ℚ)/43320000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3453914793:ℚ)/5000000000),((709733837:ℚ)/1000000000),((4213914793:ℚ)/7506250000),((7667604533:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2150489359:ℚ)/5000000000),((-48659438510536194691553171704200860822724984846506337:ℚ)/2643316041564941406250000000000000000000000000000000000),((-53945514572175231049203:ℚ)/144400000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((878381353:ℚ)/1250000000),((7216540333:ℚ)/10000000000),((1068381353:ℚ)/1906250000),((77748862997:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3907807381:ℚ)/10000000000),((-800176462713175228293932918259901761964683105183217:ℚ)/43293190002441406250000000000000000000000000000000000),((-5404493808080007871519043:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((71462573:ℚ)/100000000),((3667864179:ℚ)/5000000000),((86662573:ℚ)/154875000),((39410777611:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3472944139:ℚ)/10000000000),((-35853675854675982363834228413600955151583520599:ℚ)/1934829629516601562500000000000000000000000000000),((-4060656790060810761906601:ℚ)/10830000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((7265449697:ℚ)/10000000000),((7454903081:ℚ)/10000000000),((8785449697:ℚ)/15725000000),((79894127729:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2978139659:ℚ)/10000000000),((-440328675698022890834236349157404018089687156958897:ℚ)/23732966327667236328125000000000000000000000000000000),((-5423697331705277857046107:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((3692314329:ℚ)/5000000000),((307728599:ℚ)/400000000),((4452314329:ℚ)/8100000000),((3281557391:ℚ)/5032000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((477268887:ℚ)/2000000000),((-211256412015536931503046719199129491758516251226987:ℚ)/13668750000000000000000000000000000000000000000000000),((-11431224400583117:ℚ)/30400000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((7622948653:ℚ)/10000000000),((4799158247:ℚ)/5000000000),((9142948653:ℚ)/20000000000),((49592424223:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((7827216256435855074543350407959937:ℚ)/500000000000000000000000000000000000),((-3031737:ℚ)/8000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((9528101019:ℚ)/10000000000),((6702147707:ℚ)/5000000000),((11048101019:ℚ)/27600000000),((66719329363:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((16963202917907556369550363:ℚ)/380880000000000000000000000),((-3031737:ℚ)/8000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC25
#check @N11Formalization.C450Source21GroupedC25.bound
#print axioms N11Formalization.C450Source21GroupedC25.valid0
#print axioms N11Formalization.C450Source21GroupedC25.valid1
#print axioms N11Formalization.C450Source21GroupedC25.valid2
#print axioms N11Formalization.C450Source21GroupedC25.valid3
#print axioms N11Formalization.C450Source21GroupedC25.valid4
#print axioms N11Formalization.C450Source21GroupedC25.valid5
#print axioms N11Formalization.C450Source21GroupedC25.valid6
#print axioms N11Formalization.C450Source21GroupedC25.valid7
#print axioms N11Formalization.C450Source21GroupedC25.valid8
#print axioms N11Formalization.C450Source21GroupedC25.valid9
#print axioms N11Formalization.C450Source21GroupedC25.valid10
#print axioms N11Formalization.C450Source21GroupedC25.valid11
#print axioms N11Formalization.C450Source21GroupedC25.bound
#print axioms N11Formalization.C450Source21GroupedC25.endpoint_checks
