import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/4),((5:ℚ)/16),((1424895273:ℚ)/2500000000),((3015888749:ℚ)/5000000000),((2624895273:ℚ)/6437500000),((4999888749:ℚ)/9920000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7228175769:ℚ)/10000000000),((-82570846461619608781573301887379579043514817764383141:ℚ)/333473815917968750000000000000000000000000000000000000),((-126500498560475933393735517:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((594131999:ℚ)/1000000000),((6273098587:ℚ)/10000000000),((1074131999:ℚ)/2670000000),((10241098587:ℚ)/20600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6733248851:ℚ)/10000000000),((-1443993659239459228083982146162962507595168313235587:ℚ)/5948175937500000000000000000000000000000000000000000),((-507998804995622440409436173:ℚ)/1478656000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6182749707:ℚ)/10000000000),((6393656631:ℚ)/10000000000),((10982749707:ℚ)/27175000000),((10361656631:ℚ)/21360000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1551542951:ℚ)/2500000000),((-6092651518644790433307221725745617176503569320591301359:ℚ)/25085263730468750000000000000000000000000000000000000000),((-1544837165597311072605889711:ℚ)/4435968000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1575839771:ℚ)/2500000000),((6514151179:ℚ)/10000000000),((2775839771:ℚ)/6912500000),((10482151179:ℚ)/21740000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5927825659:ℚ)/10000000000),((-665523812234212032427225929402036275485986547738243:ℚ)/2764767951965332031250000000000000000000000000000000),((-515687892120986706191041197:ℚ)/1478656000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((80298789:ℚ)/125000000),((6634585539:ℚ)/10000000000),((46766263:ℚ)/117187500),((1514655077:ℚ)/3160000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((22550509:ℚ)/40000000),((-5626274459361670534259362042442226958242434423:ℚ)/23574102669954299926757812500000000000000000000),((-1548988610704563043802798071:ℚ)/4435968000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((261775409:ℚ)/400000000),((1350992559:ℚ)/2000000000),((453775409:ℚ)/1144000000),((2144592559:ℚ)/4500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((21334423:ℚ)/40000000),((-443007837657461489332167688283140048394282354619277:ℚ)/1871492480000000000000000000000000000000000000000000),((-62024500185169495625784031:ℚ)/177438720000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6664808573:ℚ)/10000000000),((343764291:ℚ)/500000000),((11464808573:ℚ)/29075000000),((542164291:ℚ)/1144000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5013209561:ℚ)/10000000000),((-7215731559638049083173863402154724363941632752728732209:ℚ)/30723393496093750000000000000000000000000000000000000000),((-3879839643591422248858231:ℚ)/11089920000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1696294031:ℚ)/2500000000),((3497778649:ℚ)/5000000000),((2896294031:ℚ)/7387500000),((5481778649:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1168258313:ℚ)/2500000000),((-1087732103555717713902658710364714969851352855839249:ℚ)/4666365356445312500000000000000000000000000000000000),((-129413261211023299614998917:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((6905490639:ℚ)/10000000000),((7235955483:ℚ)/10000000000),((11705490639:ℚ)/30500000000),((11203955483:ℚ)/23640000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4308353747:ℚ)/10000000000),((-8076815936509965903698275537507941392809260192448782027:ℚ)/35465781250000000000000000000000000000000000000000000000),((-1535868979302174140355491239:ℚ)/4435968000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((893246341:ℚ)/1250000000),((1929058383:ℚ)/2500000000),((1493246341:ℚ)/4050000000),((47886203:ℚ)/100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3474051837:ℚ)/10000000000),((-6040928048533921749919301893431758952918805281561371:ℚ)/27679218750000000000000000000000000000000000000000000),((-20786111007600243:ℚ)/60800000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((1906599423:ℚ)/2500000000),((9632270639:ℚ)/10000000000),((3106599423:ℚ)/10000000000),((13600270639:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-231429736302273631063580143592101188444910020821764131:ℚ)/1250000000000000000000000000000000000000000000000000000),((-182988083:ℚ)/512000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9542885501:ℚ)/10000000000),((6725499983:ℚ)/5000000000),((14342885501:ℚ)/55200000000),((8709499983:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-24649594117087113800584207735827967849616063141415179899:ℚ)/157684320000000000000000000000000000000000000000000000000),((-182988083:ℚ)/512000000)⟩
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
end N11Formalization.C450Source32GroupedC21
#check @N11Formalization.C450Source32GroupedC21.bound
#print axioms N11Formalization.C450Source32GroupedC21.valid0
#print axioms N11Formalization.C450Source32GroupedC21.valid1
#print axioms N11Formalization.C450Source32GroupedC21.valid2
#print axioms N11Formalization.C450Source32GroupedC21.valid3
#print axioms N11Formalization.C450Source32GroupedC21.valid4
#print axioms N11Formalization.C450Source32GroupedC21.valid5
#print axioms N11Formalization.C450Source32GroupedC21.valid6
#print axioms N11Formalization.C450Source32GroupedC21.valid7
#print axioms N11Formalization.C450Source32GroupedC21.valid8
#print axioms N11Formalization.C450Source32GroupedC21.valid9
#print axioms N11Formalization.C450Source32GroupedC21.valid10
#print axioms N11Formalization.C450Source32GroupedC21.valid11
#print axioms N11Formalization.C450Source32GroupedC21.bound
#print axioms N11Formalization.C450Source32GroupedC21.endpoint_checks
