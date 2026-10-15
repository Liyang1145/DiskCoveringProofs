import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/8),((3:ℚ)/16),((29233411:ℚ)/50000000),((1544111249:ℚ)/2500000000),((77233411:ℚ)/257500000),((9592333747:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1732627751:ℚ)/2500000000),((-11999208782153928288582623253098723209049552602589:ℚ)/64026972656250000000000000000000000000000000000000),((-135784787749100128580341999:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((3044361589:ℚ)/5000000000),((1283592403:ℚ)/2000000000),((7844361589:ℚ)/26700000000),((7818777209:ℚ)/20600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6415856843:ℚ)/10000000000),((-1083714185005375664081306802673200144607833836678248697:ℚ)/5948175937500000000000000000000000000000000000000000000),((-88352375624763421775623591:ℚ)/295731200000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1582608091:ℚ)/2500000000),((1634653161:ℚ)/2500000000),((3982608091:ℚ)/13587500000),((9863959483:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5863757177:ℚ)/10000000000),((-567833336929046502971929431355588642806558891335537823:ℚ)/3135657966308593750000000000000000000000000000000000000),((-141356216262527871470830079:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((3225586893:ℚ)/5000000000),((6659196449:ℚ)/10000000000),((8025586893:ℚ)/27650000000),((39817589347:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1114023451:ℚ)/2000000000),((-10544251818229156291807828588354978151002340402035047:ℚ)/58981716308593750000000000000000000000000000000000000),((-2278945761278199658161672399:ℚ)/7393280000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6571845117:ℚ)/10000000000),((169492923:ℚ)/250000000),((5390615039:ℚ)/18750000000),((143496967:ℚ)/395000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((210484301:ℚ)/400000000),((-17049241311809288139881801453642589414693137370886921:ℚ)/96559524536132812500000000000000000000000000000000000),((-1434907610414784552994071:ℚ)/4620800000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((334622501:ℚ)/500000000),((1380035461:ℚ)/2000000000),((74056591:ℚ)/260000000),((8108106383:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((617124943:ℚ)/1250000000),((-3833085501099214916843847938063168403773841068723:ℚ)/21970000000000000000000000000000000000000000000000),((-92496791481509443849839479:ℚ)/295731200000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6812991907:ℚ)/10000000000),((877572579:ℚ)/1250000000),((16412991907:ℚ)/58150000000),((5112717737:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((143472547:ℚ)/312500000),((-42391135361418981950846062728374144624434689551419848111:ℚ)/245787147968750000000000000000000000000000000000000000000),((-36385149985431160349150759:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6933473959:ℚ)/10000000000),((7140929727:ℚ)/10000000000),((16533473959:ℚ)/59100000000),((41262789181:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4219325823:ℚ)/10000000000),((-407514757156289428556897926507765737143360809652268681:ℚ)/2389179062500000000000000000000000000000000000000000000),((-2344542551376980051768483471:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((3526949571:ℚ)/5000000000),((3690737811:ℚ)/5000000000),((8326949571:ℚ)/30500000000),((20992213433:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((190699749:ℚ)/500000000),((-5882572882391581624845300027049812122017071845165951463:ℚ)/35465781250000000000000000000000000000000000000000000000),((-585042804817657157116650279:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((56988983:ℚ)/78125000),((7862022219:ℚ)/10000000000),((131988983:ℚ)/506250000),((43426066657:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2844560351:ℚ)/10000000000),((-8519398641677513794229087057852150902434862515937:ℚ)/54060974121093750000000000000000000000000000000000),((-152485307390029:ℚ)/475000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((7775399613:ℚ)/10000000000),((9778872043:ℚ)/10000000000),((17375399613:ℚ)/80000000000),((49176616129:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-83895866138361381114246006643276810651481040955695419121:ℚ)/640000000000000000000000000000000000000000000000000000000),((-170539301:ℚ)/512000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9693045637:ℚ)/10000000000),((679927269:ℚ)/500000000),((19293045637:ℚ)/110400000000),((3031781807:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-133434501858619146230613250206973251455249592874028709347:ℚ)/1261474560000000000000000000000000000000000000000000000000),((-170539301:ℚ)/512000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC19
#check @N11Formalization.C450Source32GroupedC19.bound
#print axioms N11Formalization.C450Source32GroupedC19.valid0
#print axioms N11Formalization.C450Source32GroupedC19.valid1
#print axioms N11Formalization.C450Source32GroupedC19.valid2
#print axioms N11Formalization.C450Source32GroupedC19.valid3
#print axioms N11Formalization.C450Source32GroupedC19.valid4
#print axioms N11Formalization.C450Source32GroupedC19.valid5
#print axioms N11Formalization.C450Source32GroupedC19.valid6
#print axioms N11Formalization.C450Source32GroupedC19.valid7
#print axioms N11Formalization.C450Source32GroupedC19.valid8
#print axioms N11Formalization.C450Source32GroupedC19.valid9
#print axioms N11Formalization.C450Source32GroupedC19.valid10
#print axioms N11Formalization.C450Source32GroupedC19.valid11
#print axioms N11Formalization.C450Source32GroupedC19.bound
#print axioms N11Formalization.C450Source32GroupedC19.endpoint_checks
