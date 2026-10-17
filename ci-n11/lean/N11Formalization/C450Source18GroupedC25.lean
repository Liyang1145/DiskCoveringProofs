import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((1158391189:ℚ)/2000000000),((1266389793:ℚ)/2000000000),((1414391189:ℚ)/2670000000),((13573508137:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7042467513:ℚ)/10000000000),((-1915793783843222055270833344901:ℚ)/2379270375000000000000000000000000),((-2207335713129719727919:ℚ)/7220000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6268780419:ℚ)/10000000000),((3285121779:ℚ)/5000000000),((7548780419:ℚ)/13825000000),((35006096011:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3004390107:ℚ)/5000000000),((-2152380524213558095835097427541164827076551140894701:ℚ)/313573681640625000000000000000000000000000000000000000),((-223437135712355368111661:ℚ)/722000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((1301419627:ℚ)/2000000000),((1361697023:ℚ)/2000000000),((1557419627:ℚ)/2860000000),((14431273207:ℚ)/22120000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5429328269:ℚ)/10000000000),((-539674978232571966461945431659269535561489914032529:ℚ)/73105175000000000000000000000000000000000000000000000),((-4490782473570198318123:ℚ)/14440000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1349072253:ℚ)/2000000000),((173189691:ℚ)/250000000),((1605072253:ℚ)/2907500000),((166427929:ℚ)/260000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4788019193:ℚ)/10000000000),((-569495076217544736260136422150414299679862506329517:ℚ)/57606362805175781250000000000000000000000000000000000),((-9035000223881771448491:ℚ)/28880000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6864474043:ℚ)/10000000000),((7046678783:ℚ)/10000000000),((2714824681:ℚ)/4925000000),((74300109047:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((887163433:ℚ)/2000000000),((-2803498798509386072787261686622089764382779710506609:ℚ)/279981921386718750000000000000000000000000000000000000),((-113207521949835446308093:ℚ)/361000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3491787553:ℚ)/5000000000),((3582879543:ℚ)/5000000000),((4131787553:ℚ)/7506250000),((37685915887:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4055350111:ℚ)/10000000000),((-40127619820890457392749465284705941332504378105174497:ℚ)/3964974062347412109375000000000000000000000000000000000),((-113475372327889086239477:ℚ)/361000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((7102665013:ℚ)/10000000000),((364241453:ℚ)/500000000),((8382665013:ℚ)/15250000000),((3822173077:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3637725751:ℚ)/10000000000),((-113147993749738531815816635214477760180797066401182559:ℚ)/11083056640625000000000000000000000000000000000000000000),((-9099284464976219163431:ℚ)/28880000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((7221744289:ℚ)/10000000000),((3701944591:ℚ)/5000000000),((2833914763:ℚ)/5162500000),((38757501319:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((15841229:ℚ)/50000000),((-1104976917601701422113241370211149472366329781747689:ℚ)/107490534973144531250000000000000000000000000000000000),((-12000481491638604614429:ℚ)/38000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3670406713:ℚ)/5000000000),((7522939901:ℚ)/10000000000),((4310406713:ℚ)/7862500000),((78586459109:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((261912659:ℚ)/1000000000),((-15327577711355392381995723689481440081376282162331:ℚ)/1483310395479202270507812500000000000000000000000000),((-228531858117223812233799:ℚ)/722000000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((1491974577:ℚ)/2000000000),((776101479:ℚ)/1000000000),((1747974577:ℚ)/3240000000),((8072913311:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((961631873:ℚ)/5000000000),((-33548630971359109316131657573959555759209636290657:ℚ)/3936600000000000000000000000000000000000000000000000),((-30874525163067013:ℚ)/97280000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((24056139:ℚ)/31250000),((2416157047:ℚ)/2500000000),((28056139:ℚ)/62500000),((24465413423:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((148607032355192439453303045257:ℚ)/14648437500000000000000000000000),((-20394709:ℚ)/64000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((9601682801:ℚ)/10000000000),((538754603:ℚ)/400000000),((10881682801:ℚ)/27600000000),((5283991427:ℚ)/6400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((10471589948926680994550009:ℚ)/380880000000000000000000000),((-20394709:ℚ)/64000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC25
#check @N11Formalization.C450Source18GroupedC25.bound
#print axioms N11Formalization.C450Source18GroupedC25.valid0
#print axioms N11Formalization.C450Source18GroupedC25.valid1
#print axioms N11Formalization.C450Source18GroupedC25.valid2
#print axioms N11Formalization.C450Source18GroupedC25.valid3
#print axioms N11Formalization.C450Source18GroupedC25.valid4
#print axioms N11Formalization.C450Source18GroupedC25.valid5
#print axioms N11Formalization.C450Source18GroupedC25.valid6
#print axioms N11Formalization.C450Source18GroupedC25.valid7
#print axioms N11Formalization.C450Source18GroupedC25.valid8
#print axioms N11Formalization.C450Source18GroupedC25.valid9
#print axioms N11Formalization.C450Source18GroupedC25.valid10
#print axioms N11Formalization.C450Source18GroupedC25.valid11
#print axioms N11Formalization.C450Source18GroupedC25.bound
#print axioms N11Formalization.C450Source18GroupedC25.endpoint_checks
