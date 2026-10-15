import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((280038801:ℚ)/500000000),((1229965841:ℚ)/2000000000),((976116403:ℚ)/1335000000),((18293555933:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7422578851:ℚ)/10000000000),((-15415757172783786572154096306970121:ℚ)/237927037500000000000000000000000000),((-1624956050774547769890227:ℚ)/4620800000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6076790297:ℚ)/10000000000),((638785157:ℚ)/1000000000),((20950370891:ℚ)/27650000000),((9456207041:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6442046613:ℚ)/10000000000),((-30328632284622734571635309025543863743889481586886747891:ℚ)/396357133593750000000000000000000000000000000000000000000),((-403138729483108524611083:ℚ)/1155200000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((6314745011:ℚ)/10000000000),((3312919563:ℚ)/5000000000),((21664235033:ℚ)/28600000000),((48827954319:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2950477873:ℚ)/5000000000),((-11220496908737256057514362969961980103393765877283294171:ℚ)/146210350000000000000000000000000000000000000000000000000),((-10000419295417792487192523:ℚ)/28880000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1310533887:ℚ)/2000000000),((6744820921:ℚ)/10000000000),((4475601661:ℚ)/5815000000),((99202671973:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((265606379:ℚ)/500000000),((-75553205889211410287233444980903773580236172000140341:ℚ)/921701804882812500000000000000000000000000000000000000),((-39844765395576604435288547:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((333581061:ℚ)/500000000),((6863795243:ℚ)/10000000000),((1136743183:ℚ)/1477500000),((100749338159:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1248631347:ℚ)/2500000000),((-1238860685867608787149569777702451186065873165770383:ℚ)/15119023754882812500000000000000000000000000000000000),((-39687310472514276999885883:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6790566501:ℚ)/10000000000),((436422653:ℚ)/625000000),((23091699503:ℚ)/30025000000),((6393494489:ℚ)/7387500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((186290563:ℚ)/400000000),((-41568941970673525057027119367031865607795684489278025127:ℚ)/507516679980468750000000000000000000000000000000000000000),((-154411375168200088503253:ℚ)/451250000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((6909505589:ℚ)/10000000000),((7101722869:ℚ)/10000000000),((23448516767:ℚ)/30500000000),((103842397297:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((859137349:ℚ)/2000000000),((-14517854470330662805496909081329179125160556892279761101:ℚ)/177328906250000000000000000000000000000000000000000000000),((-39370769761868458374352187:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3514219387:ℚ)/5000000000),((361033841:ℚ)/500000000),((11902658161:ℚ)/15487500000),((5269439933:ℚ)/6100000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3903010153:ℚ)/10000000000),((-158326937612807667119254634013443447504478359060657609:ℚ)/1934829629516601562500000000000000000000000000000000000),((-98029208257143878607227:ℚ)/288800000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((893420791:ℚ)/1250000000),((1467924919:ℚ)/2000000000),((3020262373:ℚ)/3931250000),((21387023947:ℚ)/24780000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3468654169:ℚ)/10000000000),((-30329048683930838903893110155882048795446063079731:ℚ)/370827598869800567626953125000000000000000000000000),((-1562082094439491066393987:ℚ)/4620800000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((3633144253:ℚ)/5000000000),((7577502707:ℚ)/10000000000),((12259432759:ℚ)/16200000000),((110027535191:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((594875201:ℚ)/2000000000),((-76045752417345114171211197895867124782884282655104431:ℚ)/984150000000000000000000000000000000000000000000000000),((-38731155897579268197625483:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((7504117687:ℚ)/10000000000),((4739939941:ℚ)/5000000000),((25232353061:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1590139057:ℚ)/10000000000),((-2512486929079652593715334817206090293023046825088795269:ℚ)/75000000000000000000000000000000000000000000000000000000),((-21440827:ℚ)/64000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((2351546841:ℚ)/2500000000),((2656533669:ℚ)/2000000000),((7734640523:ℚ)/13800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-4460934480748134872003131775283763:ℚ)/657018000000000000000000000000000000),((-21440827:ℚ)/64000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC29
#check @N11Formalization.C450Source19GroupedC29.bound
#print axioms N11Formalization.C450Source19GroupedC29.valid0
#print axioms N11Formalization.C450Source19GroupedC29.valid1
#print axioms N11Formalization.C450Source19GroupedC29.valid2
#print axioms N11Formalization.C450Source19GroupedC29.valid3
#print axioms N11Formalization.C450Source19GroupedC29.valid4
#print axioms N11Formalization.C450Source19GroupedC29.valid5
#print axioms N11Formalization.C450Source19GroupedC29.valid6
#print axioms N11Formalization.C450Source19GroupedC29.valid7
#print axioms N11Formalization.C450Source19GroupedC29.valid8
#print axioms N11Formalization.C450Source19GroupedC29.valid9
#print axioms N11Formalization.C450Source19GroupedC29.valid10
#print axioms N11Formalization.C450Source19GroupedC29.valid11
#print axioms N11Formalization.C450Source19GroupedC29.bound
#print axioms N11Formalization.C450Source19GroupedC29.endpoint_checks
