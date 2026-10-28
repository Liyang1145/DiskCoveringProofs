import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5823437301:ℚ)/10000000000),((3178862167:ℚ)/5000000000),((14548020369:ℚ)/17800000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6978246897:ℚ)/10000000000),((-1621883061302495311563136114214457973:ℚ)/35248450000000000000000000000000000000),((-77416565936797771021971483:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6298548529:ℚ)/10000000000),((6595302547:ℚ)/10000000000),((46969839703:ℚ)/55300000000),((21065907641:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5939146033:ℚ)/10000000000),((-163845026202034870572887256790418689378836417256468063069:ℚ)/3170857068750000000000000000000000000000000000000000000000),((-307189258815411935052519523:ℚ)/1478656000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((6536098409:ℚ)/10000000000),((6714089671:ℚ)/10000000000),((48632688863:ℚ)/56250000000),((21422269013:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5355012793:ℚ)/10000000000),((-20158669478813881343116442527486830864176937078964688869:ℚ)/370788574218750000000000000000000000000000000000000000000),((-305949183106946022231061627:ℚ)/1478656000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((1330974417:ℚ)/2000000000),((6832875561:ℚ)/10000000000),((9892820919:ℚ)/11440000000),((21778626683:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((252017373:ℚ)/500000000),((-4202680341900620002145997396921899157134134493358079:ℚ)/77334400000000000000000000000000000000000000000000000),((-304708057701016623040060187:ℚ)/1478656000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3386822487:ℚ)/5000000000),((3475830139:ℚ)/5000000000),((25147757409:ℚ)/29075000000),((11067490417:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4706602507:ℚ)/10000000000),((-2086289610134080034837224737762980276573924378104807961:ℚ)/38404241870117187500000000000000000000000000000000000000),((-75866470498141704389286387:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((1378483423:ℚ)/2000000000),((1402210443:ℚ)/2000000000),((10225383961:ℚ)/11725000000),((4462631329:ℚ)/4652000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2174680261:ℚ)/5000000000),((-1680073559385338730952236992080768337857456737833861947:ℚ)/30223156933593750000000000000000000000000000000000000000),((-12113776003696606573456403:ℚ)/59146240000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6951802917:ℚ)/10000000000),((7070443879:ℚ)/10000000000),((17180873473:ℚ)/19700000000),((22491331637:ℚ)/23450000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1040010907:ℚ)/2500000000),((-663809503176098921437856761801704984285787703810437977:ℚ)/11945895312500000000000000000000000000000000000000000000),((-302222655416239884640266427:ℚ)/1478656000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((109549821:ℚ)/156250000),((7129835277:ℚ)/10000000000),((811848747:ℚ)/930859375),((22669505831:ℚ)/23640000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1981120771:ℚ)/5000000000),((-1120111209474977113621304155063220820041617609910643:ℚ)/20164722035825252532958984375000000000000000000000000),((-301600647894377175706652963:ℚ)/1478656000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7070574003:ℚ)/10000000000),((449326651:ℚ)/625000000),((52374018021:ℚ)/60050000000),((1427979953:ℚ)/1489375000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3754609643:ℚ)/10000000000),((-18787967025329185441461405803327926526237285910786905421:ℚ)/338344453320312500000000000000000000000000000000000000000),((-1175696786941554639464947:ℚ)/5776000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1425991859:ℚ)/2000000000),((7248617301:ℚ)/10000000000),((10557943013:ℚ)/12105000000),((23025851903:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((883853123:ℚ)/2500000000),((-461546784133141862078067938498655300927040622542418351:ℚ)/8314490895117187500000000000000000000000000000000000000),((-300355844055276435139198547:ℚ)/1478656000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((7189344427:ℚ)/10000000000),((7308007939:ℚ)/10000000000),((53205410989:ℚ)/61000000000),((23204023817:ℚ)/24210000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((330234369:ℚ)/1000000000),((-236176964806765553394902442402355603425984617620962300487:ℚ)/4255893750000000000000000000000000000000000000000000000000),((-299733047619079812985221187:ℚ)/1478656000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((36243647:ℚ)/50000000),((1473479667:ℚ)/2000000000),((268105529:ℚ)/307375000),((4676439001:ℚ)/4880000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((3052222657:ℚ)/10000000000),((-629341408995619256491799288963195140458402778641:ℚ)/11343985427093505859375000000000000000000000000000),((-11964399523971858913736483:ℚ)/59146240000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7308114219:ℚ)/10000000000),((1485357699:ℚ)/2000000000),((18012266511:ℚ)/20650000000),((4712073097:ℚ)/4918000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((2780446377:ℚ)/10000000000),((-3052402245468613943959511026696675344097613986324065839:ℚ)/55035153906250000000000000000000000000000000000000000000),((-33073314729771488250827:ℚ)/163840000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((920937361:ℚ)/1250000000),((58949751:ℚ)/78125000),((6806561527:ℚ)/7862500000),((186849253:ℚ)/193593750),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2479899907:ℚ)/10000000000),((-160987935602964141181614414607928565824545319040783:ℚ)/2966620790958404541015625000000000000000000000000000),((-18142042875489609276347:ℚ)/90250000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((3743133893:ℚ)/5000000000),((1556624957:ℚ)/2000000000),((27641937251:ℚ)/32400000000),((4925874871:ℚ)/5032000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1732180057:ℚ)/10000000000),((-409613514976671904757797672295294669088420888600145873:ℚ)/7873200000000000000000000000000000000000000000000000000),((-102724109:ℚ)/512000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((3861901961:ℚ)/5000000000),((9683481137:ℚ)/10000000000),((28473313727:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-2250184701372002325134643368303441405409337326613135469:ℚ)/75000000000000000000000000000000000000000000000000000000),((-102724109:ℚ)/512000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((9624031201:ℚ)/10000000000),((2696779883:ℚ)/2000000000),((70248218407:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-6206845148051663444476505165730556589:ℚ)/336393216000000000000000000000000000000),((-102724109:ℚ)/512000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((2421:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source11 nn0 nn1 Qcell ((2459:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC31
#check @N11Formalization.C450Source11GroupedC31.bound
#print axioms N11Formalization.C450Source11GroupedC31.valid0
#print axioms N11Formalization.C450Source11GroupedC31.valid1
#print axioms N11Formalization.C450Source11GroupedC31.valid2
#print axioms N11Formalization.C450Source11GroupedC31.valid3
#print axioms N11Formalization.C450Source11GroupedC31.valid4
#print axioms N11Formalization.C450Source11GroupedC31.valid5
#print axioms N11Formalization.C450Source11GroupedC31.valid6
#print axioms N11Formalization.C450Source11GroupedC31.valid7
#print axioms N11Formalization.C450Source11GroupedC31.valid8
#print axioms N11Formalization.C450Source11GroupedC31.valid9
#print axioms N11Formalization.C450Source11GroupedC31.valid10
#print axioms N11Formalization.C450Source11GroupedC31.valid11
#print axioms N11Formalization.C450Source11GroupedC31.valid12
#print axioms N11Formalization.C450Source11GroupedC31.valid13
#print axioms N11Formalization.C450Source11GroupedC31.valid14
#print axioms N11Formalization.C450Source11GroupedC31.valid15
#print axioms N11Formalization.C450Source11GroupedC31.valid16
#print axioms N11Formalization.C450Source11GroupedC31.bound
#print axioms N11Formalization.C450Source11GroupedC31.endpoint_checks
