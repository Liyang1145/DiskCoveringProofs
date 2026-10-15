import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((1574348217:ℚ)/2500000000),((131814563:ℚ)/200000000),((-71014563:ℚ)/496000000),((-1523044651:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((23767451:ℚ)/40000000),((370686754250483596418287369665070597101102928864920109989:ℚ)/3308060253906250000000000000000000000000000000000000000000),((-58002776700739071055688793:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((3268284269:ℚ)/5000000000),((853737981:ℚ)/1250000000),((-473737981:ℚ)/3218750000),((-3404852807:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5353800393:ℚ)/10000000000),((906388636623018586659465186171722826937466657100198933827:ℚ)/8168828287500000000000000000000000000000000000000000000000),((-264119934469928704710843857:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((677562379:ℚ)/1000000000),((3474723659:ℚ)/5000000000),((-651574553:ℚ)/4450000000),((-752687137:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1175214397:ℚ)/2500000000),((77926898945631955270427823649485584375691257492315105113:ℚ)/714428311043750000000000000000000000000000000000000000000),((-11853491260948766561029217:ℚ)/147865600000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((6895110257:ℚ)/10000000000),((7068963261:ℚ)/10000000000),((-4028963261:ℚ)/27175000000),((-7885330771:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((868188563:ℚ)/2000000000),((15608046491695737791524257059975712697499740868581807841037:ℚ)/143613401405468750000000000000000000000000000000000000000000),((-1249948527236158686993186313:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((876821399:ℚ)/1250000000),((718845309:ℚ)/1000000000),((-414845309:ℚ)/2765000000),((-1030464197:ℚ)/14062500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((790138607:ℚ)/2000000000),((4066852490159638635960039518237967055840728101577466621:ℚ)/37545058876276016235351562500000000000000000000000000000),((-20541541450025033129098937:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((222937747:ℚ)/312500000),((3653959061:ℚ)/5000000000),((-711319687:ℚ)/4687500000),((-268813241:ℚ)/3575000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1759996933:ℚ)/5000000000),((92513825397510011062541031963813926953219526656806707:ℚ)/856701269531250000000000000000000000000000000000000000),((-1347148568423774074394833:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((1450684323:ℚ)/2000000000),((7427359587:ℚ)/10000000000),((-337489199:ℚ)/2200000000),((-1792052969:ℚ)/23260000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3031609921:ℚ)/10000000000),((93167211694852544797734023632170942539051677121153839819:ℚ)/865170760850000000000000000000000000000000000000000000000),((-57776542416922603520090673:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7372813463:ℚ)/10000000000),((7546778633:ℚ)/10000000000),((-4506778633:ℚ)/29075000000),((-9318440389:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((306406061:ℚ)/1250000000),((11938218684571768837592831549231633216148027913387491029949:ℚ)/111144609987500000000000000000000000000000000000000000000000),((-1509459480566143973439700153:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((1498436903:ℚ)/2000000000),((7785553707:ℚ)/10000000000),((-4745553707:ℚ)/29550000000),((-1935310709:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((843205703:ℚ)/5000000000),((5795845420402203893874977035846240238599997965455213211411:ℚ)/53658308400000000000000000000000000000000000000000000000000),((-62984736366027314954324633:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((966358519:ℚ)/1250000000),((8262877901:ℚ)/10000000000),((-5222877901:ℚ)/30500000000),((-1299075557:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((19659800214457345308742435196157210855138857770856017873:ℚ)/180099450000000000000000000000000000000000000000000000000),((-113128571:ℚ)/1024000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((4104012893:ℚ)/5000000000),((10169954867:ℚ)/10000000000),((-7129954867:ℚ)/32400000000),((-5912038679:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((30258107753366241635428674119432735989200869700815627340911:ℚ)/259200000000000000000000000000000000000000000000000000000000),((-113128571:ℚ)/1024000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10114596379:ℚ)/10000000000),((6989121861:ℚ)/5000000000),((-5469121861:ℚ)/20000000000),((-17543789137:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2197171616860469840272932912165155561804894562429898382897:ℚ)/16819660800000000000000000000000000000000000000000000000000),((-113128571:ℚ)/1024000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC13
#check @N11Formalization.C450Source21GroupedC13.bound
#print axioms N11Formalization.C450Source21GroupedC13.valid0
#print axioms N11Formalization.C450Source21GroupedC13.valid1
#print axioms N11Formalization.C450Source21GroupedC13.valid2
#print axioms N11Formalization.C450Source21GroupedC13.valid3
#print axioms N11Formalization.C450Source21GroupedC13.valid4
#print axioms N11Formalization.C450Source21GroupedC13.valid5
#print axioms N11Formalization.C450Source21GroupedC13.valid6
#print axioms N11Formalization.C450Source21GroupedC13.valid7
#print axioms N11Formalization.C450Source21GroupedC13.valid8
#print axioms N11Formalization.C450Source21GroupedC13.valid9
#print axioms N11Formalization.C450Source21GroupedC13.valid10
#print axioms N11Formalization.C450Source21GroupedC13.valid11
#print axioms N11Formalization.C450Source21GroupedC13.bound
#print axioms N11Formalization.C450Source21GroupedC13.endpoint_checks
