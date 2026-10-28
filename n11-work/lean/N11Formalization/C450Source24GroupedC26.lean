import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5583264769:ℚ)/10000000000),((1535056989:ℚ)/2500000000),((64329382921:ℚ)/106800000000),((1903056989:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1864150663:ℚ)/2500000000),((-14881523942285308399689687458039005247:ℚ)/152273304000000000000000000000000000000),((-13973578575966198671294203:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((1212250541:ℚ)/2000000000),((6379102217:ℚ)/10000000000),((13726254869:ℚ)/22120000000),((7851102217:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((51808093:ℚ)/80000000),((-1686450906426541643859773347753839936693581591144802461:ℚ)/14495346600000000000000000000000000000000000000000000000),((-224531209873367580137447827:ℚ)/591462400000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((6300091361:ℚ)/10000000000),((6498504243:ℚ)/10000000000),((70780822249:ℚ)/112500000000),((7970504243:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2967758727:ℚ)/5000000000),((-185111470694743451522455719414782933890718356436865224927:ℚ)/1483154296875000000000000000000000000000000000000000000000),((-224977170497105592177390107:ℚ)/591462400000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6419476501:ℚ)/10000000000),((6617884439:ℚ)/10000000000),((71855288509:ℚ)/114400000000),((8089884439:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1412129403:ℚ)/2500000000),((-53025661343584197526013056079870854052364865787650850011:ℚ)/425339200000000000000000000000000000000000000000000000000),((-224634870296556061593634003:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6538840381:ℚ)/10000000000),((1684310971:ℚ)/2500000000),((72929563429:ℚ)/116300000000),((2052310971:ℚ)/2860000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2673969059:ℚ)/5000000000),((-459012926305889375484963755298879915638685696003205036747:ℚ)/3686807219531250000000000000000000000000000000000000000000),((-14017026500540533349133163:ℚ)/36966400000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((1664546013:ℚ)/2500000000),((685658359:ℚ)/1000000000),((18500914117:ℚ)/29550000000),((832858359:ℚ)/1163000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2515658449:ℚ)/5000000000),((-7518043928000354138391759732483170188418920554974619931:ℚ)/60476095019531250000000000000000000000000000000000000000),((-2238898390898380021844883:ℚ)/5914624000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((3388754249:ℚ)/5000000000),((6975904503:ℚ)/10000000000),((37538788241:ℚ)/60050000000),((8447904503:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2347689919:ℚ)/5000000000),((-251943644485780268578458695477804780043673104059285531903:ℚ)/2030066719921875000000000000000000000000000000000000000000),((-223487122531807025370730387:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((6896814641:ℚ)/10000000000),((709520751:ℚ)/1000000000),((76151331769:ℚ)/122000000000),((856720751:ℚ)/1201000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4335607671:ℚ)/10000000000),((-702946490748521109264402620627718293795119278226930377149:ℚ)/5674525000000000000000000000000000000000000000000000000000),((-2230642808792991572983043:ℚ)/5914624000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7016103343:ℚ)/10000000000),((293350523:ℚ)/400000000),((77224930087:ℚ)/125800000000),((352230523:ℚ)/488000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((3945451669:ℚ)/10000000000),((-181015136542880060671311708429022226078008961131695861243:ℚ)/1555363681250000000000000000000000000000000000000000000000),((-354225860378716429850347:ℚ)/946339840000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((3627315807:ℚ)/5000000000),((7572256351:ℚ)/10000000000),((39685842263:ℚ)/64800000000),((9044256351:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1513136187:ℚ)/5000000000),((-3656565368606867909799018666320281927817610471067878169:ℚ)/31492800000000000000000000000000000000000000000000000000),((-220404896373780039303404643:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((468318701:ℚ)/625000000),((947849613:ℚ)/1000000000),((5094868309:ℚ)/10000000000),((1095049613:ℚ)/1296000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((419806381:ℚ)/2500000000),((-26543612110960490451883792551932430942608821245536803:ℚ)/585937500000000000000000000000000000000000000000000000),((-5695933071582931:ℚ)/15200000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((2349794477:ℚ)/2500000000),((13285806401:ℚ)/10000000000),((24668150293:ℚ)/55200000000),((14757806401:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6475875327646450702820657:ℚ)/761760000000000000000000000),((-384916321:ℚ)/1024000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC26
#check @N11Formalization.C450Source24GroupedC26.bound
#print axioms N11Formalization.C450Source24GroupedC26.valid0
#print axioms N11Formalization.C450Source24GroupedC26.valid1
#print axioms N11Formalization.C450Source24GroupedC26.valid2
#print axioms N11Formalization.C450Source24GroupedC26.valid3
#print axioms N11Formalization.C450Source24GroupedC26.valid4
#print axioms N11Formalization.C450Source24GroupedC26.valid5
#print axioms N11Formalization.C450Source24GroupedC26.valid6
#print axioms N11Formalization.C450Source24GroupedC26.valid7
#print axioms N11Formalization.C450Source24GroupedC26.valid8
#print axioms N11Formalization.C450Source24GroupedC26.valid9
#print axioms N11Formalization.C450Source24GroupedC26.valid10
#print axioms N11Formalization.C450Source24GroupedC26.valid11
#print axioms N11Formalization.C450Source24GroupedC26.bound
#print axioms N11Formalization.C450Source24GroupedC26.endpoint_checks
