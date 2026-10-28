import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7127726669:ℚ)/10000000000),((3649687501:ℚ)/5000000000),(-1:ℚ),((-18055180007:ℚ)/20030000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((885971919:ℚ)/2500000000),((30310472023541494677379729568971873:ℚ)/80240180000000000000000000000000000),((4123984203476786302312873:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((7187194521:ℚ)/10000000000),((7358750003:ℚ)/10000000000),(-1:ℚ),((-18233583563:ℚ)/20220000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((827764107:ℚ)/2500000000),((257046187299930000712826467181320111:ℚ)/681414000000000000000000000000000000),((16560287623156749132690857:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((452916289:ℚ)/625000000),((3694218751:ℚ)/5000000000),(-1:ℚ),((-1150748867:ℚ)/1269687500),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((3061267999:ℚ)/10000000000),((355108120202045317047596668271147:ℚ)/948297851562500000000000000000000),((4148129774152625186687873:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1455278607:ℚ)/2000000000),((3709062501:ℚ)/5000000000),(-1:ℚ),((-3700235821:ℚ)/4082000000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((732167303:ℚ)/2500000000),((4612306603693545444281250477809:ℚ)/12324500000000000000000000000000),((12468590963590257413188619:ℚ)/10830000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7306125027:ℚ)/10000000000),((3723906251:ℚ)/5000000000),(-1:ℚ),((-18590375081:ℚ)/20505000000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((2789966341:ℚ)/10000000000),((131046327129693779704937805619338623:ℚ)/350379187500000000000000000000000000),((4164273546650303583562873:ℚ)/3610000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((3667928303:ℚ)/5000000000),((3738750001:ℚ)/5000000000),(-1:ℚ),((-9339784909:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((1322099153:ℚ)/5000000000),((198277428257254733431576639391875521:ℚ)/530450000000000000000000000000000000),((4172359450513278524187873:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7365587777:ℚ)/10000000000),((3768437501:ℚ)/5000000000),(-1:ℚ),((-18768763331:ℚ)/20790000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((622530989:ℚ)/2500000000),((920722226324401772920870869968611:ℚ)/2450250000000000000000000000000000),((4188559293467499889812873:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((185626223:ℚ)/250000000),((3798125001:ℚ)/5000000000),(-1:ℚ),((-473678669:ℚ)/524500000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2149825311:ℚ)/10000000000),((64530672637297987416341662350173:ℚ)/171937656250000000000000000000000),((12614389550178249703813619:ℚ)/10830000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((7484508499:ℚ)/10000000000),((3857500001:ℚ)/5000000000),(-1:ℚ),((-19125525497:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1745559771:ℚ)/10000000000),((432353175189274638523635409981895279:ℚ)/1140624000000000000000000000000000000),((145631:ℚ)/125000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((7603423133:ℚ)/10000000000),((8190000003:ℚ)/10000000000),(-1:ℚ),((-19482269399:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((1047128915416523295094839129484561631:ℚ)/2617472000000000000000000000000000000),((145631:ℚ)/125000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((8079026883:ℚ)/10000000000),((4570000001:ℚ)/5000000000),(-1:ℚ),((-20909080649:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1402517298090378802163781183807677629:ℚ)/3359232000000000000000000000000000000),((145631:ℚ)/125000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((4515010811:ℚ)/5000000000),((5520000001:ℚ)/5000000000),(-1:ℚ),((-11881032433:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((562662225784720433407406117788314879:ℚ)/1280000000000000000000000000000000000),((145631:ℚ)/125000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((2732860869:ℚ)/2500000000),((14840000003:ℚ)/10000000000),(-1:ℚ),((-7366582607:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((29239368903882358147748299:ℚ)/60940800000000000000000000),((145631:ℚ)/125000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((2003:ℚ)/3200) ((4063:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((4063:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source27 nn0 nn1 Qcell ((4063:ℚ)/6400) ((103:ℚ)/160) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC01
#check @N11Formalization.C450Source27GroupedC01.bound
#print axioms N11Formalization.C450Source27GroupedC01.valid0
#print axioms N11Formalization.C450Source27GroupedC01.valid1
#print axioms N11Formalization.C450Source27GroupedC01.valid2
#print axioms N11Formalization.C450Source27GroupedC01.valid3
#print axioms N11Formalization.C450Source27GroupedC01.valid4
#print axioms N11Formalization.C450Source27GroupedC01.valid5
#print axioms N11Formalization.C450Source27GroupedC01.valid6
#print axioms N11Formalization.C450Source27GroupedC01.valid7
#print axioms N11Formalization.C450Source27GroupedC01.valid8
#print axioms N11Formalization.C450Source27GroupedC01.valid9
#print axioms N11Formalization.C450Source27GroupedC01.valid10
#print axioms N11Formalization.C450Source27GroupedC01.valid11
#print axioms N11Formalization.C450Source27GroupedC01.valid12
#print axioms N11Formalization.C450Source27GroupedC01.bound
#print axioms N11Formalization.C450Source27GroupedC01.endpoint_checks
