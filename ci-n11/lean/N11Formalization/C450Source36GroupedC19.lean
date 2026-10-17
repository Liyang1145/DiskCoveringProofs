import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/8),((3:ℚ)/16),((5783069139:ℚ)/10000000000),((382781131:ℚ)/625000000),((16663069139:ℚ)/51500000000),((2548343393:ℚ)/6200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1765127107:ℚ)/2500000000),((-359729163685050003649434990386383039646667994455152539625113:ℚ)/1230598414453125000000000000000000000000000000000000000000000),((-3977862452608118042069409:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1506600979:ℚ)/2500000000),((24398029:ℚ)/39062500),((4226600979:ℚ)/13112500000),((160694087:ℚ)/402343750),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((6551642163:ℚ)/10000000000),((-5432622988809387525984381487441588133781882718411259467691:ℚ)/18686199592958068847656250000000000000000000000000000000000),((-508451526075584938053653:ℚ)/1805000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((1229581437:ℚ)/2000000000),((3183597751:ℚ)/5000000000),((3405581437:ℚ)/10680000000),((20750793253:ℚ)/52450000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1256915499:ℚ)/2000000000),((-300568177780195510654762709543372989678889945907260469945917:ℚ)/1047260599968150000000000000000000000000000000000000000000000),((-262010132326100399376625119:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((24489489:ℚ)/39062500),((1297680729:ℚ)/2000000000),((133978978:ℚ)/424609375),((8373042187:ℚ)/21360000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3003774749:ℚ)/5000000000),((-39605463689703324679575758351269740846128302105041090872539:ℚ)/139711200475108337402343750000000000000000000000000000000000),((-42183495848675937179644479:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((6390615457:ℚ)/10000000000),((1309794959:ℚ)/2000000000),((5756871819:ℚ)/18275000000),((8409384877:ℚ)/21740000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1429767093:ℚ)/2500000000),((-1593584786906468893191265599425541048918751856749697063659939:ℚ)/5634057505505114746093750000000000000000000000000000000000000),((-42631672178082840034153039:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6451234317:ℚ)/10000000000),((6609524783:ℚ)/10000000000),((17331234317:ℚ)/55300000000),((42228574349:ℚ)/109650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2784983297:ℚ)/5000000000),((-3722238139844027858646161707358043162950346270251136565083439:ℚ)/13237362141518115234375000000000000000000000000000000000000000),((-1068947173064546117742600591:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((1302366229:ℚ)/2000000000),((667005417:ℚ)/1000000000),((3478366229:ℚ)/11155000000),((4241016251:ℚ)/11060000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((5417262291:ℚ)/10000000000),((-3311289065316135218562967075032976821654743928243264929243:ℚ)/11843797829238696289062500000000000000000000000000000000000),((-10720567458172444670469791:ℚ)/36966400000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6572406527:ℚ)/10000000000),((6730563499:ℚ)/10000000000),((17452406527:ℚ)/56250000000),((42591690497:ℚ)/111550000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((328789787:ℚ)/625000000),((-9019055901643125770137379262646957181882813146456205227657301:ℚ)/32441283783316612243652343750000000000000000000000000000000000),((-1075120601065527306586560119:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((6632961027:ℚ)/10000000000),((3425762027:ℚ)/5000000000),((17512961027:ℚ)/57200000000),((21477286081:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2549861501:ℚ)/5000000000),((-12980138700940019880612995463323159964941453653564455526147:ℚ)/47372153400000000000000000000000000000000000000000000000000),((-268281381759121098406565751:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((3377004773:ℚ)/5000000000),((6972410419:ℚ)/10000000000),((8817004773:ℚ)/29075000000),((43317231257:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1190815233:ℚ)/2500000000),((-425920582323811672721572772012036332773482931784950888093773:ℚ)/1570656684004052734375000000000000000000000000000000000000000),((-1078939548440826478846714759:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((3437490421:ℚ)/5000000000),((70932263:ℚ)/100000000),((8877490421:ℚ)/29550000000),((436796789:ℚ)/1163000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4403494997:ℚ)/10000000000),((-813414134089302641695999623849888472938560204913712471283309:ℚ)/3029558939424902343750000000000000000000000000000000000000000),((-5708272892103095799269:ℚ)/19456000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((6995878777:ℚ)/10000000000),((7334660221:ℚ)/10000000000),((17875878777:ℚ)/61000000000),((44403980663:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1003529053:ℚ)/2500000000),((-7203930332450885823958800623169281315242172675664220998723953:ℚ)/27527830090625000000000000000000000000000000000000000000000000),((-1079353140991771106205735079:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((7237468747:ℚ)/10000000000),((1954205099:ℚ)/2500000000),((671017361:ℚ)/2400000000),((11462615297:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1550574387:ℚ)/5000000000),((-13390932914115350989615127370058357865902917915566130403:ℚ)/53582400000000000000000000000000000000000000000000000000),((-286090402478942927:ℚ)/972800000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((1543982461:ℚ)/2000000000),((4869273409:ℚ)/5000000000),((3719982461:ℚ)/16000000000),((25807820227:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-5957142115386870077546612521493742850905629610561551810063:ℚ)/27993600000000000000000000000000000000000000000000000000000),((-78599047:ℚ)/256000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9642494003:ℚ)/10000000000),((13563874183:ℚ)/10000000000),((20522494003:ℚ)/110400000000),((63091622549:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-566908057047408989929528042025266921672522634806878280769:ℚ)/3153686400000000000000000000000000000000000000000000000000),((-78599047:ℚ)/256000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC19
#check @N11Formalization.C450Source36GroupedC19.bound
#print axioms N11Formalization.C450Source36GroupedC19.valid0
#print axioms N11Formalization.C450Source36GroupedC19.valid1
#print axioms N11Formalization.C450Source36GroupedC19.valid2
#print axioms N11Formalization.C450Source36GroupedC19.valid3
#print axioms N11Formalization.C450Source36GroupedC19.valid4
#print axioms N11Formalization.C450Source36GroupedC19.valid5
#print axioms N11Formalization.C450Source36GroupedC19.valid6
#print axioms N11Formalization.C450Source36GroupedC19.valid7
#print axioms N11Formalization.C450Source36GroupedC19.valid8
#print axioms N11Formalization.C450Source36GroupedC19.valid9
#print axioms N11Formalization.C450Source36GroupedC19.valid10
#print axioms N11Formalization.C450Source36GroupedC19.valid11
#print axioms N11Formalization.C450Source36GroupedC19.valid12
#print axioms N11Formalization.C450Source36GroupedC19.valid13
#print axioms N11Formalization.C450Source36GroupedC19.valid14
#print axioms N11Formalization.C450Source36GroupedC19.bound
#print axioms N11Formalization.C450Source36GroupedC19.endpoint_checks
