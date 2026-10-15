import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5956386041:ℚ)/10000000000),((3239701187:ℚ)/5000000000),((70000246451:ℚ)/106800000000),((334164631:ℚ)/400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((670139541:ℚ)/1000000000),((-3775503950668177274628075520611866561:ℚ)/304546608000000000000000000000000000000),((-36233724001798857156637307:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1607910837:ℚ)/2500000000),((6717008849:ℚ)/10000000000),((18807019207:ℚ)/27650000000),((21431026547:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5618539527:ℚ)/10000000000),((-5975722500054079527480096359582002077718226907417307397:ℚ)/396357133593750000000000000000000000000000000000000000000),((-2265977845611827268767443:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((6669258731:ℚ)/10000000000),((1708952347:ℚ)/2500000000),((77841846041:ℚ)/112500000000),((5446857041:ℚ)/6912500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5001011919:ℚ)/10000000000),((-48403490446322654326188439538164973310864663206530078619:ℚ)/2966308593750000000000000000000000000000000000000000000000),((-36268357709004155150045267:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((3394031749:ℚ)/5000000000),((3477304123:ℚ)/5000000000),((39574349239:ℚ)/57200000000),((11071912369:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((233229629:ℚ)/500000000),((-1740574449834712224925061073664173095477171840808105453:ℚ)/106334800000000000000000000000000000000000000000000000000),((-9066350731169784329663347:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((1726716611:ℚ)/2500000000),((219187721:ℚ)/312500000),((20113882721:ℚ)/28837500000),((63414833:ℚ)/81250000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((172160683:ℚ)/400000000),((-1905654101799714940322344833477117666261559740563165779:ℚ)/112412369778442382812500000000000000000000000000000000000),((-2267030551193491307096387:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3483133631:ℚ)/5000000000),((1768351377:ℚ)/2500000000),((40554469941:ℚ)/58150000000),((5625054131:ℚ)/7209375000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((4112693401:ℚ)/10000000000),((-834133049351860451001402890264307894291519426026252813:ℚ)/49157429593750000000000000000000000000000000000000000000),((-9067816734520355367333867:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((7025667659:ℚ)/10000000000),((1783200891:ℚ)/2500000000),((81762344249:ℚ)/117250000000),((5669602673:ℚ)/7268750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3912582519:ℚ)/10000000000),((-18332489178135483032312000749499259665604551043135729037:ℚ)/1079398461914062500000000000000000000000000000000000000000),((-36270118076117364736287507:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((7085067643:ℚ)/10000000000),((7192201249:ℚ)/10000000000),((27471914691:ℚ)/39400000000),((22856603747:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3702255973:ℚ)/10000000000),((-1624500208589446675505562885022953607632663222915477587:ℚ)/95567162500000000000000000000000000000000000000000000000),((-1908896959544580002587937:ℚ)/12160000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((3572233613:ℚ)/5000000000),((1812899643:ℚ)/2500000000),((41534569743:ℚ)/59575000000),((5758698929:ℚ)/7387500000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1739928921:ℚ)/5000000000),((-22481914320567638306246107012960118834025100896693261831:ℚ)/1321515223339843750000000000000000000000000000000000000000),((-9067009850636113258407843:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((7203866417:ℚ)/10000000000),((3655497771:ℚ)/5000000000),((83722530587:ℚ)/120100000000),((11606493313:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3242901153:ℚ)/10000000000),((-11520714846995385409227642848745293038647402372507539979:ℚ)/676688906640625000000000000000000000000000000000000000000),((-36267109588095511383897483:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((907908153:ℚ)/1250000000),((7370392167:ℚ)/10000000000),((10546989683:ℚ)/15131250000),((23391176501:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2987919587:ℚ)/10000000000),((-13662812187136446060253186869140035336407407366171113:ℚ)/801937779235839843750000000000000000000000000000000000),((-566660199788189373718923:ℚ)/3610000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((3661331829:ℚ)/5000000000),((1485957691:ℚ)/2000000000),((42514650119:ℚ)/61000000000),((4713873073:ℚ)/6052500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2709824687:ℚ)/10000000000),((-24185683571598172826203516826736100889167591222544432207:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-9066367249132038176788627:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3691030863:ℚ)/5000000000),((7548580051:ℚ)/10000000000),((42841339493:ℚ)/61950000000),((23925740153:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((96023663:ℚ)/400000000),((-2050965015801748158394913226761102128693624898075407327:ℚ)/123829096289062500000000000000000000000000000000000000000),((-9063752521498201375784843:ℚ)/57760000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((3750428401:ℚ)/5000000000),((7667370389:ℚ)/10000000000),((43494712411:ℚ)/62900000000),((24282111167:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((404252697:ℚ)/2500000000),((-25200133467608278956147818497912871593835222894234067:ℚ)/1518909844970703125000000000000000000000000000000000000),((-9066216154387560681639947:ℚ)/57760000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((1523930103:ℚ)/2000000000),((7904947517:ℚ)/10000000000),((17659231133:ℚ)/25920000000),((24994842551:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-63252924992113949983298044252063111200501500596320407:ℚ)/4031078400000000000000000000000000000000000000000000000),((-251249:ℚ)/1600000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7857234093:ℚ)/10000000000),((9805432601:ℚ)/10000000000),((90909575023:ℚ)/160000000000),((30696297803:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-31195830764490701751697657246188654730520000325958104917:ℚ)/4800000000000000000000000000000000000000000000000000000000),((-251249:ℚ)/1600000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((9757759747:ℚ)/10000000000),((13606001959:ℚ)/10000000000),((37271785739:ℚ)/73600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-54279695868570678782572981020120409:ℚ)/99672064000000000000000000000000000000),((-251249:ℚ)/1600000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC28
#check @N11Formalization.C450NinthGroupedC28.bound
#print axioms N11Formalization.C450NinthGroupedC28.valid0
#print axioms N11Formalization.C450NinthGroupedC28.valid1
#print axioms N11Formalization.C450NinthGroupedC28.valid2
#print axioms N11Formalization.C450NinthGroupedC28.valid3
#print axioms N11Formalization.C450NinthGroupedC28.valid4
#print axioms N11Formalization.C450NinthGroupedC28.valid5
#print axioms N11Formalization.C450NinthGroupedC28.valid6
#print axioms N11Formalization.C450NinthGroupedC28.valid7
#print axioms N11Formalization.C450NinthGroupedC28.valid8
#print axioms N11Formalization.C450NinthGroupedC28.valid9
#print axioms N11Formalization.C450NinthGroupedC28.valid10
#print axioms N11Formalization.C450NinthGroupedC28.valid11
#print axioms N11Formalization.C450NinthGroupedC28.valid12
#print axioms N11Formalization.C450NinthGroupedC28.valid13
#print axioms N11Formalization.C450NinthGroupedC28.valid14
#print axioms N11Formalization.C450NinthGroupedC28.valid15
#print axioms N11Formalization.C450NinthGroupedC28.valid16
#print axioms N11Formalization.C450NinthGroupedC28.bound
#print axioms N11Formalization.C450NinthGroupedC28.endpoint_checks
