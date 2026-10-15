import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5671936741:ℚ)/10000000000),((3107625561:ℚ)/5000000000),((14621185729:ℚ)/17800000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3641496527:ℚ)/5000000000),((-5028561881863932558240754179345353229:ℚ)/70496900000000000000000000000000000000),((-525556437434729983349473621:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((3073577411:ℚ)/5000000000),((1290582879:ℚ)/2000000000),((23595041877:ℚ)/27650000000),((4230148637:ℚ)/4272000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6286261183:ℚ)/10000000000),((-10665366598086727028321985110191142700007561662646064523:ℚ)/132119044531250000000000000000000000000000000000000000000),((-129987903100154119816461061:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((798094077:ℚ)/1250000000),((669056681:ℚ)/1000000000),((6106658539:ℚ)/7150000000),((2186370043:ℚ)/2212000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5733305671:ℚ)/10000000000),((-184586399830936758120539066461509492448604575880451741:ℚ)/2284536718750000000000000000000000000000000000000000000),((-8036452334515937236607789:ℚ)/28880000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((662234391:ℚ)/1000000000),((6809389279:ℚ)/10000000000),((5051640737:ℚ)/5815000000),((22220167837:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5128268049:ℚ)/10000000000),((-104554893441565357847768955493742503253255065257416303:ℚ)/1228935739843750000000000000000000000000000000000000000),((-5115322606751848130445421:ℚ)/18483200000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((3370568659:ℚ)/5000000000),((866026177:ℚ)/1250000000),((25673980613:ℚ)/29550000000),((2822078531:ℚ)/2907500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2400034329:ℚ)/5000000000),((-1142710985475186795620370555900375414978715042991964761:ℚ)/13439132226562500000000000000000000000000000000000000000),((-127180900088102342564278821:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((685992933:ℚ)/1000000000),((3493809323:ℚ)/5000000000),((5217950531:ℚ)/5957500000),((11377427969:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4449730169:ℚ)/10000000000),((-115084620104414573494470818121386001272247817917965341:ℚ)/1321515223339843750000000000000000000000000000000000000),((-5073236801133199848833749:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3459662417:ℚ)/5000000000),((7047027333:ℚ)/10000000000),((26297636919:ℚ)/30025000000),((22933081999:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((10661397:ℚ)/25000000),((-3681344345790589212995545345519118782679929590342267081:ℚ)/42293056665039062500000000000000000000000000000000000000),((-126479878629217371912569149:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1744680003:ℚ)/2500000000),((7106435491:ℚ)/10000000000),((13252760021:ℚ)/15131250000),((23111306473:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((407151263:ℚ)/1000000000),((-156986362081302577364033253416691420096209188717799833:ℚ)/1804360003280639648437500000000000000000000000000000000),((-31532212445159916634078069:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((3519057437:ℚ)/5000000000),((1791460783:ℚ)/2500000000),((26713402059:ℚ)/30500000000),((5822382349:ℚ)/6052500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((967352371:ℚ)/2500000000),((-15421568404328417852546142611832144952845229075405121541:ℚ)/177328906250000000000000000000000000000000000000000000000),((-125777833411501887152903429:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((7097509427:ℚ)/10000000000),((1806312567:ℚ)/2500000000),((53842565989:ℚ)/61475000000),((5866937701:ℚ)/6100000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((3656744081:ℚ)/10000000000),((-7889030606361628651999294307106490318476572314601902059:ℚ)/90751883416748046875000000000000000000000000000000000000),((-501707317802634098010745189:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7156903677:ℚ)/10000000000),((7284656911:ℚ)/10000000000),((54258325739:ℚ)/61950000000),((23645970733:ℚ)/24590000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((686309829:ℚ)/2000000000),((-43040587271616059439395774536640398736502291100880010703:ℚ)/495316385156250000000000000000000000000000000000000000000),((-500303351307797595038677189:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((225509301:ℚ)/312500000),((3701734381:ℚ)/5000000000),((1708565107:ℚ)/1965625000),((12001203143:ℚ)/12390000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3191168853:ℚ)/10000000000),((-1007298690201626215650512634419288228018171765261453:ℚ)/11866483163833618164062500000000000000000000000000000),((-971662047166151909454007:ℚ)/3610000000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((3667542341:ℚ)/5000000000),((382054351:ℚ)/500000000),((3083644043:ℚ)/3600000000),((1235763053:ℚ)/1258000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((52961637:ℚ)/200000000),((-2628657028722663114803630673428772741066479662787477:ℚ)/32400000000000000000000000000000000000000000000000000),((-123210146819701791267660821:ℚ)/462080000000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((3786327761:ℚ)/5000000000),((38167323:ℚ)/40000000),((28584294327:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((424270979:ℚ)/5000000000),((-1116249642454621123504847980177935526587775238237531337:ℚ)/25000000000000000000000000000000000000000000000000000000),((-123214875800337174637739261:ℚ)/462080000000000000000000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((9473101067:ℚ)/10000000000),((13029984:ℚ)/9765625),((70471707469:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2851410517871749481323824316652519011:ℚ)/112131072000000000000000000000000000000),((-17065849:ℚ)/64000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC31
#check @N11Formalization.C450Source15GroupedC31.bound
#print axioms N11Formalization.C450Source15GroupedC31.valid0
#print axioms N11Formalization.C450Source15GroupedC31.valid1
#print axioms N11Formalization.C450Source15GroupedC31.valid2
#print axioms N11Formalization.C450Source15GroupedC31.valid3
#print axioms N11Formalization.C450Source15GroupedC31.valid4
#print axioms N11Formalization.C450Source15GroupedC31.valid5
#print axioms N11Formalization.C450Source15GroupedC31.valid6
#print axioms N11Formalization.C450Source15GroupedC31.valid7
#print axioms N11Formalization.C450Source15GroupedC31.valid8
#print axioms N11Formalization.C450Source15GroupedC31.valid9
#print axioms N11Formalization.C450Source15GroupedC31.valid10
#print axioms N11Formalization.C450Source15GroupedC31.valid11
#print axioms N11Formalization.C450Source15GroupedC31.valid12
#print axioms N11Formalization.C450Source15GroupedC31.valid13
#print axioms N11Formalization.C450Source15GroupedC31.valid14
#print axioms N11Formalization.C450Source15GroupedC31.bound
#print axioms N11Formalization.C450Source15GroupedC31.endpoint_checks
