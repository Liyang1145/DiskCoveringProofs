import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6619124679:ℚ)/10000000000),((1708176049:ℚ)/2500000000),((-1128176049:ℚ)/3100000000),((-9044624251:ℚ)/33700000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1284223669:ℚ)/2500000000),((195027573325338882894540688245356056281:ℚ)/845833519750000000000000000000000000000),((2415847401122361114423419781:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((842444859:ℚ)/1250000000),((1738265687:ℚ)/2500000000),((-1158265687:ℚ)/3159375000),((-3497114013:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1201141067:ℚ)/2500000000),((3352276571953859874786443284894979604330075545044865809:ℚ)/14520965930593013763427734375000000000000000000000000000),((36137478537556823907694221:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6859929651:ℚ)/10000000000),((3506609767:ℚ)/5000000000),((-2346609767:ℚ)/6437500000),((-9606502519:ℚ)/34650000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1112432297:ℚ)/2500000000),((238413666413628350806001793163110304796618331417271659023:ℚ)/1042646267062425613403320312500000000000000000000000000000),((6118137417898811529773781:ℚ)/40960000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((865011547:ℚ)/1250000000),((1414672377:ℚ)/2000000000),((-950672377:ℚ)/2598750000),((-3655080829:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4262116631:ℚ)/10000000000),((210897996091494724063608615196374290218846583660687867:ℚ)/921572404870605468750000000000000000000000000000000000),((33689974251819858004091469:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((3490120277:ℚ)/5000000000),((3566745099:ℚ)/5000000000),((-2406745099:ℚ)/6556250000),((-14830841939:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2033228649:ℚ)/5000000000),((24766386219150309938716119439100198593773668968296274845169:ℚ)/108134777227870178222656250000000000000000000000000000000000),((525848265152869527514127789:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((3520187293:ℚ)/5000000000),((7193604859:ℚ)/10000000000),((-4873604859:ℚ)/13231250000),((-15041311051:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1930761283:ℚ)/5000000000),((1642856092646887680065183475596143893972628069385518915143:ℚ)/7167086962754535675048828125000000000000000000000000000000),((512587897035957352304915709:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((7100494859:ℚ)/10000000000),((1813426559:ℚ)/2500000000),((-1233426559:ℚ)/3337500000),((-30503464013:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((227858921:ℚ)/625000000),((1100215010973046456816093096847418974053470999565493370133:ℚ)/4795742666345214843750000000000000000000000000000000000000),((1997033794214663303023594221:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7160601747:ℚ)/10000000000),((7313794687:ℚ)/10000000000),((-4993794687:ℚ)/13468750000),((-30924212229:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((13668231:ℚ)/40000000),((4142978510023199683874437881203710027014050941580386893761469:ℚ)/18043508188796806335449218750000000000000000000000000000000000),((1943439542475082672555642269:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7220695609:ℚ)/10000000000),((1474774111:ℚ)/2000000000),((-1010774111:ℚ)/2717500000),((-1843815839:ℚ)/6450000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3172671761:ℚ)/10000000000),((3330982691282889387842557278981466492681116166503408653:ℚ)/14494578949261474609375000000000000000000000000000000000),((5234262334736087008931261:ℚ)/40960000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7280776791:ℚ)/10000000000),((7433934173:ℚ)/10000000000),((-5113934173:ℚ)/13706250000),((-31765437537:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((18178893:ℚ)/62500000),((2924974481332829836090646747175428682093877442156257666987:ℚ)/12716724480436706542968750000000000000000000000000000000000),((1835421150043015082946114021:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((1835211407:ℚ)/2500000000),((7554025927:ℚ)/10000000000),((-5234025927:ℚ)/13825000000),((-8046479849:ℚ)/28125000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((523792589:ℚ)/2000000000),((2115751369807126757408501488660170270842812571995289423:ℚ)/9100036230468750000000000000000000000000000000000000000),((111312297633595545316219509:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((3730473773:ℚ)/5000000000),((383703619:ℚ)/500000000),((-267703619:ℚ)/703125000),((-16513316411:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1915851889:ℚ)/10000000000),((681200489344380313981665571251582291268749849726359929:ℚ)/2925252914428710937500000000000000000000000000000000000),((417829254227859985209058589:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((1516200763:ℚ)/2000000000),((4316528353:ℚ)/5000000000),((-286957123:ℚ)/650000000),((-6773405341:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((707183143:ℚ)/10000000000),((82255352329162935983204222063705421787509824951710769:ℚ)/312815039062500000000000000000000000000000000000000000),((62421143027192639690354829:ℚ)/591462400000000000000000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((427002801:ℚ)/500000000),((1054585341:ℚ)/1000000000),((-822585341:ℚ)/1620000000),((-2029019607:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1880735824008125445814675585333208909:ℚ)/6480000000000000000000000000000000000),((4273943:ℚ)/40960000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((522647451:ℚ)/500000000),((3590203483:ℚ)/2500000000),((-3010203483:ℚ)/5000000000),((-899510719:ℚ)/3680000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2325178546946557336746351:ℚ)/6771200000000000000000000),((4273943:ℚ)/40960000)⟩
theorem valid14 : Valid source31 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source31 nn0 nn1 Qcell ((2079:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source31 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((45:ℚ)/64) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC09
#check @N11Formalization.C450Source31GroupedC09.bound
#print axioms N11Formalization.C450Source31GroupedC09.valid0
#print axioms N11Formalization.C450Source31GroupedC09.valid1
#print axioms N11Formalization.C450Source31GroupedC09.valid2
#print axioms N11Formalization.C450Source31GroupedC09.valid3
#print axioms N11Formalization.C450Source31GroupedC09.valid4
#print axioms N11Formalization.C450Source31GroupedC09.valid5
#print axioms N11Formalization.C450Source31GroupedC09.valid6
#print axioms N11Formalization.C450Source31GroupedC09.valid7
#print axioms N11Formalization.C450Source31GroupedC09.valid8
#print axioms N11Formalization.C450Source31GroupedC09.valid9
#print axioms N11Formalization.C450Source31GroupedC09.valid10
#print axioms N11Formalization.C450Source31GroupedC09.valid11
#print axioms N11Formalization.C450Source31GroupedC09.valid12
#print axioms N11Formalization.C450Source31GroupedC09.valid13
#print axioms N11Formalization.C450Source31GroupedC09.valid14
#print axioms N11Formalization.C450Source31GroupedC09.bound
#print axioms N11Formalization.C450Source31GroupedC09.endpoint_checks
