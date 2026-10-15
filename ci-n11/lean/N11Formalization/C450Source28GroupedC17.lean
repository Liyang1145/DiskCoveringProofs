import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(0:ℚ),((1:ℚ)/16),((301904201:ℚ)/500000000),((6352936823:ℚ)/10000000000),((416:ℚ)/2575),((23632936823:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6526376861:ℚ)/10000000000),((216885649836175721136473024873528371080529:ℚ)/2589103874048000000000000000000000000000000),((-4612402589158561217851919529:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((6279118191:ℚ)/10000000000),((824185441:ℚ)/1250000000),((208:ℚ)/1335),((2984185441:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5984678517:ℚ)/10000000000),((34394567092774937875549762724167935935722481301582439181:ℚ)/412725952482223510742187500000000000000000000000000000000),((-74776345346429256108496281:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((407493477:ℚ)/625000000),((839209441:ℚ)/1250000000),((832:ℚ)/5435),((2999209441:ℚ)/13350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5396647367:ℚ)/10000000000),((4304307059800001380409602355570804463401806002602406787459223:ℚ)/52711352207219531250000000000000000000000000000000000000000000),((-77604112847919042666064281:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6640196719:ℚ)/10000000000),((6833817109:ℚ)/10000000000),((416:ℚ)/2765),((24113817109:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((254009273:ℚ)/500000000),((37597392288118557115716304681338527826598388051764274311685603:ℚ)/460277964969055078125000000000000000000000000000000000000000000),((-5052767647156727391041769681:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((3380221751:ℚ)/5000000000),((1390782177:ℚ)/2000000000),((832:ℚ)/5625),((4846782177:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1186191123:ℚ)/2500000000),((21330705289633448473748700336717501323771266302498454273:ℚ)/260916238800000000000000000000000000000000000000000000000),((-205547294986402248194245529:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((17201597:ℚ)/25000000),((707395929:ℚ)/1000000000),((8:ℚ)/55),((811798643:ℚ)/3750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4385997203:ℚ)/10000000000),((3264693513186134734519103251354188744938266921104259727:ℚ)/39880371093750000000000000000000000000000000000000000000),((-52244096212973058921472841:ℚ)/147865600000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7000785239:ℚ)/10000000000),((1438792919:ℚ)/2000000000),((832:ℚ)/5815),((4894792919:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3997560829:ℚ)/10000000000),((6227720191725669763627112386214212420615558326394007854401097:ℚ)/75939681365433600000000000000000000000000000000000000000000000),((-212398058072559939148496361:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7120885269:ℚ)/10000000000),((7313928923:ℚ)/10000000000),((416:ℚ)/2955),((24593928923:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((892434507:ℚ)/2500000000),((7839951345970238149624176100692306363874741057480432033113183:ℚ)/95387534255192187500000000000000000000000000000000000000000000),((-5395309792433850502998006129:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((7240941179:ℚ)/10000000000),((1888435613:ℚ)/2500000000),((208:ℚ)/1525),((6208435613:ℚ)/29550000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3086141583:ℚ)/10000000000),((150496815317739820814308187844895181254005216835703095179619:ℚ)/1800252396541406250000000000000000000000000000000000000000000),((-341945061037431389281503969:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((233779033:ℚ)/312500000),((8032957117:ℚ)/10000000000),((52:ℚ)/405),((25312957117:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((886236753:ℚ)/5000000000),((534769823920606659325000136281934231953823263247319869427899:ℚ)/6205093087500000000000000000000000000000000000000000000000000),((-2907154676051391:ℚ)/7600000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((79604609:ℚ)/100000000),((4972886487:ℚ)/5000000000),((13:ℚ)/125),((168060327:ℚ)/800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((19347704103721217223462373347412164450209535214643:ℚ)/200000000000000000000000000000000000000000000000000),((-398184267:ℚ)/1024000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9874238087:ℚ)/10000000000),((3440188949:ℚ)/2500000000),((26:ℚ)/345),((7760188949:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1033039774659141116948536313104807405403:ℚ)/8464000000000000000000000000000000000000),((-398184267:ℚ)/1024000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC17
#check @N11Formalization.C450Source28GroupedC17.bound
#print axioms N11Formalization.C450Source28GroupedC17.valid0
#print axioms N11Formalization.C450Source28GroupedC17.valid1
#print axioms N11Formalization.C450Source28GroupedC17.valid2
#print axioms N11Formalization.C450Source28GroupedC17.valid3
#print axioms N11Formalization.C450Source28GroupedC17.valid4
#print axioms N11Formalization.C450Source28GroupedC17.valid5
#print axioms N11Formalization.C450Source28GroupedC17.valid6
#print axioms N11Formalization.C450Source28GroupedC17.valid7
#print axioms N11Formalization.C450Source28GroupedC17.valid8
#print axioms N11Formalization.C450Source28GroupedC17.valid9
#print axioms N11Formalization.C450Source28GroupedC17.valid10
#print axioms N11Formalization.C450Source28GroupedC17.valid11
#print axioms N11Formalization.C450Source28GroupedC17.bound
#print axioms N11Formalization.C450Source28GroupedC17.endpoint_checks
