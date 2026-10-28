import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((3155807269:ℚ)/5000000000),((1657190551:ℚ)/2500000000),((-537190551:ℚ)/6200000000),((-187421807:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1477088537:ℚ)/2500000000),((1740739816701491117115425868549680457:ℚ)/20390498000000000000000000000000000000),((-68321829628751057614634607:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6552799557:ℚ)/10000000000),((6749327681:ℚ)/10000000000),((-2269327681:ℚ)/25750000000),((-1098398671:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5311789591:ℚ)/10000000000),((39122793861541868975724855983376975584594085936901315672571:ℚ)/458693650637435913085937500000000000000000000000000000000000),((-314074575763334119238748463:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((3336644861:ℚ)/5000000000),((858728391:ℚ)/1250000000),((-298728391:ℚ)/3278125000),((-729934583:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4989939641:ℚ)/10000000000),((1811025941683403840828431573644567561330289792289196397957:ℚ)/20927521959066009521484375000000000000000000000000000000000),((-83658756887477202383800127:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/4),((-3:ℚ)/16),((6793716653:ℚ)/10000000000),((6930053213:ℚ)/10000000000),((-2450053213:ℚ)/26700000000),((-1821149959:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4648025577:ℚ)/10000000000),((212395781967928888087089248932630243012431908099434888942847:ℚ)/2455420245168750000000000000000000000000000000000000000000000),((-355307276938111955270956383:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((171347687:ℚ)/250000000),((3495132053:ℚ)/5000000000),((-1255132053:ℚ)/13468750000),((-50043061:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4468102941:ℚ)/10000000000),((1571595038336109911143435718599212717128043972105652834513623:ℚ)/18043508188796806335449218750000000000000000000000000000000000),((-228553406809841518766103:ℚ)/1848320000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((3457041879:ℚ)/5000000000),((3525230107:ℚ)/5000000000),((-1285230107:ℚ)/13587500000),((-64183861:ℚ)/3225000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4281199933:ℚ)/10000000000),((158878551217979749972842808002483206640583517874554060017:ℚ)/1811822368657684326171875000000000000000000000000000000000),((-94022930270946846155358967:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((6974245873:ℚ)/10000000000),((3555320963:ℚ)/5000000000),((-438440321:ℚ)/4568750000),((-2362737619:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4086353509:ℚ)/10000000000),((22009913772419951911119317569547267736929647371785603471:ℚ)/249347538832092285156250000000000000000000000000000000000),((-386526132351965448436746023:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7034394201:ℚ)/10000000000),((1446192733:ℚ)/2000000000),((-550192733:ℚ)/5530000000),((-2543182603:ℚ)/112500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3882362341:ℚ)/10000000000),((367033094440922923156265333842278473288064049043479427:ℚ)/4076816231250000000000000000000000000000000000000000000),((-396988728598159335071176087:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((7154650929:ℚ)/10000000000),((735123219:ℚ)/1000000000),((-287123219:ℚ)/2812500000),((-2903952787:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3440348109:ℚ)/10000000000),((533106393254870670225301834097213730925112148968014861:ℚ)/5850505828857421875000000000000000000000000000000000000),((-417998643022136113729817767:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1818714171:ℚ)/2500000000),((3795810057:ℚ)/5000000000),((-1555810057:ℚ)/14300000000),((-816142513:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2935663273:ℚ)/10000000000),((16750316724553988220730106570925943900560859685806874580523:ℚ)/177321171035937500000000000000000000000000000000000000000000),((-27445111489013823197573167:ℚ)/184832000000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((7515125339:ℚ)/10000000000),((7831825047:ℚ)/10000000000),((-3351825047:ℚ)/29550000000),((-3985376017:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1495898863:ℚ)/10000000000),((6428564597208153990659244701193142564802671979351478179893:ℚ)/66676014686718750000000000000000000000000000000000000000000),((-481708917323684896052457327:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((3877609341:ℚ)/5000000000),((4155875841:ℚ)/5000000000),((-1915875841:ℚ)/15250000000),((-2352828023:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1242255102308329304269059342805042647163572912909629756153:ℚ)/12119322436523437500000000000000000000000000000000000000000),((-34409237:ℚ)/204800000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((1646988473:ℚ)/2000000000),((2045344963:ℚ)/2000000000),((-1149344963:ℚ)/6480000000),((-1228965419:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((508762531384927436538166645552673972742271580219971:ℚ)/3936600000000000000000000000000000000000000000000000),((-34409237:ℚ)/204800000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((5074650389:ℚ)/5000000000),((14044217537:ℚ)/10000000000),((-9564217537:ℚ)/40000000000),((-5943951167:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4282876685048734841621515358320213489843:ℚ)/25392000000000000000000000000000000000000),((-34409237:ℚ)/204800000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC13
#check @N11Formalization.C450Source30GroupedC13.bound
#print axioms N11Formalization.C450Source30GroupedC13.valid0
#print axioms N11Formalization.C450Source30GroupedC13.valid1
#print axioms N11Formalization.C450Source30GroupedC13.valid2
#print axioms N11Formalization.C450Source30GroupedC13.valid3
#print axioms N11Formalization.C450Source30GroupedC13.valid4
#print axioms N11Formalization.C450Source30GroupedC13.valid5
#print axioms N11Formalization.C450Source30GroupedC13.valid6
#print axioms N11Formalization.C450Source30GroupedC13.valid7
#print axioms N11Formalization.C450Source30GroupedC13.valid8
#print axioms N11Formalization.C450Source30GroupedC13.valid9
#print axioms N11Formalization.C450Source30GroupedC13.valid10
#print axioms N11Formalization.C450Source30GroupedC13.valid11
#print axioms N11Formalization.C450Source30GroupedC13.valid12
#print axioms N11Formalization.C450Source30GroupedC13.valid13
#print axioms N11Formalization.C450Source30GroupedC13.bound
#print axioms N11Formalization.C450Source30GroupedC13.endpoint_checks
