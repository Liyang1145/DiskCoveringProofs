import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/16),((1:ℚ)/8),((5921711691:ℚ)/10000000000),((97657987:ℚ)/156250000),((25121711691:ℚ)/103000000000),((252657987:ℚ)/775000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6774516279:ℚ)/10000000000),((-210172844018476348523351989584925324202206377579913644183:ℚ)/1365908750000000000000000000000000000000000000000000000000),((-241430283028264252187747:ℚ)/902500000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6163847301:ℚ)/10000000000),((1622919311:ℚ)/2500000000),((8454615767:ℚ)/35600000000),((4102919311:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3124406717:ℚ)/5000000000),((-2095178915881109518449663984022274213745908148852415819:ℚ)/14099380000000000000000000000000000000000000000000000000),((-15840749272123112391188237:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6405644021:ℚ)/10000000000),((1653087763:ℚ)/2500000000),((25605644021:ℚ)/108700000000),((1377695921:ℚ)/4450000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((88787943:ℚ)/156250000),((-235754697443854523608405083612166657106458265017598411793:ℚ)/1605456878750000000000000000000000000000000000000000000000),((-16319790986622095207151093:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((1631606699:ℚ)/2500000000),((6732957203:ℚ)/10000000000),((918800957:ℚ)/3950000000),((16652957203:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1344974969:ℚ)/2500000000),((-521846369048014667438107228467338314482407351740963:ℚ)/3611125488281250000000000000000000000000000000000000),((-264151160500919751820609973:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6647137989:ℚ)/10000000000),((6853499231:ℚ)/10000000000),((2871904221:ℚ)/12500000000),((16773499231:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5061378257:ℚ)/10000000000),((-1356956844114673669027022853414816110417431899565233:ℚ)/9536743164062500000000000000000000000000000000000000),((-267155606200851051591174317:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((6767781343:ℚ)/10000000000),((278959217:ℚ)/400000000),((25967781343:ℚ)/114400000000),((675759217:ℚ)/2250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((944717581:ℚ)/2000000000),((-262324087759655332758110102503030876640292788396544267491:ℚ)/1871492480000000000000000000000000000000000000000000000000),((-432208217182858466352333:ℚ)/1478656000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3444180173:ℚ)/5000000000),((1773600963:ℚ)/2500000000),((13044180173:ℚ)/58150000000),((4253600963:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((872402337:ℚ)/2000000000),((-33954938706063760878012247749624653487855071551698480609:ℚ)/245787147968750000000000000000000000000000000000000000000),((-51201540417908032803044479:ℚ)/173280000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((3504439123:ℚ)/5000000000),((57718179:ℚ)/80000000),((13104439123:ℚ)/59100000000),((137078179:ℚ)/465200000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((496263839:ℚ)/1250000000),((-325452412896057911160759968783339416747331473751618613:ℚ)/2389179062500000000000000000000000000000000000000000000),((-52990074167572567044031:ℚ)/177438720000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7129338077:ℚ)/10000000000),((186383881:ℚ)/250000000),((26329338077:ℚ)/122000000000),((144794627:ℚ)/492500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1768886313:ℚ)/5000000000),((-898971123065455587837949779510388356487510752723407029867:ℚ)/6809430000000000000000000000000000000000000000000000000000),((-173219983543925195851917:ℚ)/577600000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7370094681:ℚ)/10000000000),((1587193809:ℚ)/2000000000),((8856698227:ℚ)/43200000000),((3571193809:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((493189293:ℚ)/2000000000),((-4186382105690232711458125644205333503135788507200108733:ℚ)/33592320000000000000000000000000000000000000000000000000),((-37394636817254951:ℚ)/121600000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((1962756073:ℚ)/2500000000),((2463255553:ℚ)/2500000000),((6762756073:ℚ)/40000000000),((183083539:ℚ)/600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-24537687476071844868469287453259997716366518384518965343:ℚ)/240000000000000000000000000000000000000000000000000000000),((-20286967:ℚ)/64000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((1221129087:ℚ)/1250000000),((2734586333:ℚ)/2000000000),((1207043029:ℚ)/9200000000),((4718586333:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-57834130745763826485738863834977527576593104927396211:ℚ)/730020000000000000000000000000000000000000000000000000),((-20286967:ℚ)/64000000)⟩
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
end N11Formalization.C450Source32GroupedC18
#check @N11Formalization.C450Source32GroupedC18.bound
#print axioms N11Formalization.C450Source32GroupedC18.valid0
#print axioms N11Formalization.C450Source32GroupedC18.valid1
#print axioms N11Formalization.C450Source32GroupedC18.valid2
#print axioms N11Formalization.C450Source32GroupedC18.valid3
#print axioms N11Formalization.C450Source32GroupedC18.valid4
#print axioms N11Formalization.C450Source32GroupedC18.valid5
#print axioms N11Formalization.C450Source32GroupedC18.valid6
#print axioms N11Formalization.C450Source32GroupedC18.valid7
#print axioms N11Formalization.C450Source32GroupedC18.valid8
#print axioms N11Formalization.C450Source32GroupedC18.valid9
#print axioms N11Formalization.C450Source32GroupedC18.valid10
#print axioms N11Formalization.C450Source32GroupedC18.valid11
#print axioms N11Formalization.C450Source32GroupedC18.bound
#print axioms N11Formalization.C450Source32GroupedC18.endpoint_checks
