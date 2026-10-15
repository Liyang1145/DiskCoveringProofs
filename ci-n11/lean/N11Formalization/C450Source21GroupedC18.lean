import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6048983653:ℚ)/10000000000),((329213153:ℚ)/500000000),((18208983653:ℚ)/106800000000),((649213153:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3251362121:ℚ)/5000000000),((25560275419161394195816001932715963509:ℚ)/271842636672000000000000000000000000000),((-1152403593834109504903301:ℚ)/4620800000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6527640981:ℚ)/10000000000),((1364651557:ℚ)/2000000000),((18687640981:ℚ)/110600000000),((881550519:ℚ)/3560000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1344195307:ℚ)/2500000000),((1096063317869810047735727337902680163761599625785380108687:ℚ)/12319192281200000000000000000000000000000000000000000000000),((-19665106031444693232040061:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6766779173:ℚ)/10000000000),((6942716939:ℚ)/10000000000),((6308926391:ℚ)/37500000000),((13342716939:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((29540533:ℚ)/62500000),((118178137250570563861074036889901662095205189036060499323:ℚ)/1358938743750000000000000000000000000000000000000000000000),((-506932276981848253247370269:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((3443153179:ℚ)/5000000000),((1765538083:ℚ)/2500000000),((9523153179:ℚ)/57200000000),((3365538083:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((873680807:ℚ)/2000000000),((10243015332667779145179201447584450854622898173915249624131:ℚ)/118472743034362792968750000000000000000000000000000000000000),((-1691658484779836918052159:ℚ)/6080000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3502903741:ℚ)/5000000000),((7181565143:ℚ)/10000000000),((9582903741:ℚ)/58150000000),((13581565143:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3980547321:ℚ)/10000000000),((34016608248488620278079492142700408084082122450944587236842817:ℚ)/395519173778300000000000000000000000000000000000000000000000000),((-521583812910934408538931861:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((7125283837:ℚ)/10000000000),((7300956473:ℚ)/10000000000),((19285283837:ℚ)/118200000000),((13700956473:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((355313863:ℚ)/1000000000),((3061902263472209624447820848319783105238433759566325886214429:ℚ)/35770325345697070312500000000000000000000000000000000000000000),((-27836382296782210900418199:ℚ)/97280000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((7244736633:ℚ)/10000000000),((7420327351:ℚ)/10000000000),((19404736633:ℚ)/120100000000),((13820327351:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((24557257:ℚ)/80000000),((158621549344662814371171847861429382111846256571861666328960609:ℚ)/1860923305221693750000000000000000000000000000000000000000000000),((-536186612147003069235883989:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7364167001:ℚ)/10000000000),((942459843:ℚ)/1250000000),((19524167001:ℚ)/122000000000),((1742459843:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2497698253:ℚ)/10000000000),((1670505805880535319743816218404238971287125706840892385051:ℚ)/19671557981326293945312500000000000000000000000000000000000),((-25475153144432146428966983:ℚ)/86640000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7483576001:ℚ)/10000000000),((4008453377:ℚ)/5000000000),((6547858667:ℚ)/43200000000),((7208453377:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((876305299:ℚ)/5000000000),((2797966285190483889497027711951198284444812859072031906663:ℚ)/32318193164062500000000000000000000000000000000000000000000),((-4531888157901429:ℚ)/15200000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((7961017303:ℚ)/10000000000),((4961845659:ℚ)/5000000000),((20121017303:ℚ)/160000000000),((8161845659:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1216530769799672601710898270604296417098170282422921989:ℚ)/13286025000000000000000000000000000000000000000000000000),((-1547999:ℚ)/5120000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((2467112557:ℚ)/2500000000),((6865819223:ℚ)/5000000000),((5507112557:ℚ)/55200000000),((10065819223:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((8206197254033189885888632071379367476211:ℚ)/76176000000000000000000000000000000000000),((-1547999:ℚ)/5120000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC18
#check @N11Formalization.C450Source21GroupedC18.bound
#print axioms N11Formalization.C450Source21GroupedC18.valid0
#print axioms N11Formalization.C450Source21GroupedC18.valid1
#print axioms N11Formalization.C450Source21GroupedC18.valid2
#print axioms N11Formalization.C450Source21GroupedC18.valid3
#print axioms N11Formalization.C450Source21GroupedC18.valid4
#print axioms N11Formalization.C450Source21GroupedC18.valid5
#print axioms N11Formalization.C450Source21GroupedC18.valid6
#print axioms N11Formalization.C450Source21GroupedC18.valid7
#print axioms N11Formalization.C450Source21GroupedC18.valid8
#print axioms N11Formalization.C450Source21GroupedC18.valid9
#print axioms N11Formalization.C450Source21GroupedC18.valid10
#print axioms N11Formalization.C450Source21GroupedC18.bound
#print axioms N11Formalization.C450Source21GroupedC18.endpoint_checks
