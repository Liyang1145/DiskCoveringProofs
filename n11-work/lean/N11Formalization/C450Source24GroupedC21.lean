import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((2925299373:ℚ)/5000000000),((1600098657:ℚ)/2500000000),((4685299373:ℚ)/13350000000),((2336098657:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((138448819:ℚ)/200000000),((69312524618566896514624314942318280321:ℚ)/1087370546688000000000000000000000000000),((-8003829054548605486223593:ℚ)/22179840000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6330043443:ℚ)/10000000000),((41498659:ℚ)/62500000),((9850043443:ℚ)/27650000000),((59898659:ℚ)/133500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((18327131:ℚ)/31250000),((4641277749574653479574497549924024960899112614889773:ℚ)/86345208952734375000000000000000000000000000000000000),((-1741628508041866584389:ℚ)/4620800000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((1313906759:ℚ)/2000000000),((3379716199:ℚ)/5000000000),((2017906759:ℚ)/5625000000),((4851716199:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2634079713:ℚ)/5000000000),((345910479774784642986115899420295147763482135990712461:ℚ)/6988827825000000000000000000000000000000000000000000000),((-11382219149292193874839219:ℚ)/29573120000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((3344613971:ℚ)/5000000000),((1375809847:ℚ)/2000000000),((5104613971:ℚ)/14300000000),((218289983:ℚ)/500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4945938503:ℚ)/10000000000),((393349899521066207261167234625581739510794926433310613:ℚ)/7987890625000000000000000000000000000000000000000000000),((-1836075393946832523669971:ℚ)/4731699200000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((1361778073:ℚ)/2000000000),((874829681:ℚ)/1250000000),((2065778073:ℚ)/5815000000),((1242829681:ℚ)/2860000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4603284671:ℚ)/10000000000),((3637390610168226165021919253939058958613583938342419104833:ℚ)/74159845083431250000000000000000000000000000000000000000000),((-722990609785350473436259:ℚ)/1848320000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3464261321:ℚ)/5000000000),((1779549609:ℚ)/2500000000),((26519093:ℚ)/75000000),((2515549609:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((169408247:ℚ)/400000000),((7512807309424928617606994102116084232577474368238059:ℚ)/153616967480468750000000000000000000000000000000000000),((-8744517500661498644930617:ℚ)/22179840000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((7048126249:ℚ)/10000000000),((723773351:ℚ)/1000000000),((10568126249:ℚ)/30025000000),((339391117:ℚ)/788000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3834350397:ℚ)/10000000000),((322990402343181474092486445728282108536512643553849233541:ℚ)/6616616196343800000000000000000000000000000000000000000000),((-469999748299252409805619:ℚ)/1182924800000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((1791925641:ℚ)/2500000000),((1471448779:ℚ)/2000000000),((2671925641:ℚ)/7625000000),((2060248779:ℚ)/4804000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3389065349:ℚ)/10000000000),((62877101057252589060105986763251852308342004436281715641:ℚ)/1289195223864200000000000000000000000000000000000000000000),((-1894362003684380883976779:ℚ)/4731699200000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((7287252881:ℚ)/10000000000),((7596195129:ℚ)/10000000000),((10807252881:ℚ)/31450000000),((10540195129:ℚ)/24400000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2878760453:ℚ)/10000000000),((232352657517395841457753819436911164075479632553714479132931:ℚ)/4490149491050000000000000000000000000000000000000000000000000),((-142503757508866358647278937:ℚ)/354877440000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7526280293:ℚ)/10000000000),((1958765131:ℚ)/2500000000),((1227364477:ℚ)/3600000000),((2694765131:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((696982199:ℚ)/5000000000),((3260768872532364192649999394587478261487137449045807441:ℚ)/62992229090625000000000000000000000000000000000000000000),((-399879898586833157:ℚ)/972800000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((3882608659:ℚ)/5000000000),((4871816939:ℚ)/5000000000),((5642608659:ℚ)/20000000000),((6343816939:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((104396049857385305180960711562319069745815001942154467:ℚ)/1275458400000000000000000000000000000000000000000000000),((-423945741:ℚ)/1024000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9674239617:ℚ)/10000000000),((13553670537:ℚ)/10000000000),((13194239617:ℚ)/55200000000),((16497670537:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((92304080473364944688030777:ℚ)/761760000000000000000000000),((-423945741:ℚ)/1024000000)⟩
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
end N11Formalization.C450Source24GroupedC21
#check @N11Formalization.C450Source24GroupedC21.bound
#print axioms N11Formalization.C450Source24GroupedC21.valid0
#print axioms N11Formalization.C450Source24GroupedC21.valid1
#print axioms N11Formalization.C450Source24GroupedC21.valid2
#print axioms N11Formalization.C450Source24GroupedC21.valid3
#print axioms N11Formalization.C450Source24GroupedC21.valid4
#print axioms N11Formalization.C450Source24GroupedC21.valid5
#print axioms N11Formalization.C450Source24GroupedC21.valid6
#print axioms N11Formalization.C450Source24GroupedC21.valid7
#print axioms N11Formalization.C450Source24GroupedC21.valid8
#print axioms N11Formalization.C450Source24GroupedC21.valid9
#print axioms N11Formalization.C450Source24GroupedC21.valid10
#print axioms N11Formalization.C450Source24GroupedC21.valid11
#print axioms N11Formalization.C450Source24GroupedC21.bound
#print axioms N11Formalization.C450Source24GroupedC21.endpoint_checks
