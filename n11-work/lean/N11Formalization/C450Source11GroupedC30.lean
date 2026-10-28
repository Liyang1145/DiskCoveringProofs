import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((2923487533:ℚ)/5000000000),((6379200029:ℚ)/10000000000),((40885337929:ℚ)/53400000000),((47854400203:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((433119239:ℚ)/625000000),((-35548248190711091869893442090020051089:ℚ)/951708150000000000000000000000000000000),((-189107099834611326636694311:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6322190417:ℚ)/10000000000),((6616813463:ℚ)/10000000000),((87948475421:ℚ)/110600000000),((49517694241:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4596349:ℚ)/7812500),((-1074349880278479300458995127640318755952771859111598280167:ℚ)/25366856550000000000000000000000000000000000000000000000000),((-188064207981205270991909599:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((1639946747:ℚ)/2500000000),((1347123461:ℚ)/2000000000),((22759307711:ℚ)/28125000000),((10069864227:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((661701407:ℚ)/1250000000),((-2072832884160355047922281976133284919213559183343024837:ℚ)/46348571777343750000000000000000000000000000000000000000),((-7501706477592027395957591:ℚ)/36966400000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((267143313:ℚ)/400000000),((1713604839:ℚ)/2500000000),((336660279:ℚ)/416000000),((12795233873:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((995073271:ℚ)/2000000000),((-20124727411394735831072071128201842503746908933639:ℚ)/449945600000000000000000000000000000000000000000000),((-35066446614059754147438973:ℚ)/173280000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6797377139:ℚ)/10000000000),((3486609853:ℚ)/5000000000),((94125902807:ℚ)/116300000000),((26006268971:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1159317247:ℚ)/2500000000),((-329831400213312241406652109731928196337289915092456550061:ℚ)/7373614439062500000000000000000000000000000000000000000000),((-46624841898729487941329639:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((1729042501:ℚ)/2500000000),((7032619269:ℚ)/10000000000),((23917552513:ℚ)/29312500000),((52428334883:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((42745831:ℚ)/100000000),((-15777488091929090092888845094555472642871671619376477:ℚ)/344195938110351562500000000000000000000000000000000000),((-558715504784601221276338693:ℚ)/2772480000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1395113183:ℚ)/2000000000),((1773004609:ℚ)/2500000000),((19288471379:ℚ)/23640000000),((13211032263:ℚ)/14656250000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4081980179:ℚ)/10000000000),((-315344068978194917644511770847042639147703228321266473:ℚ)/6880835700000000000000000000000000000000000000000000000),((-11623601159191192571703151:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((703496149:ℚ)/1000000000),((3575708609:ℚ)/5000000000),((9721449937:ℚ)/11915000000),((8876653421:ℚ)/9850000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1940195039:ℚ)/5000000000),((-1453252188848204587777267309007119178209682084912695171:ℚ)/31716365360156250000000000000000000000000000000000000000),((-46429179600888035959415151:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((7094356737:ℚ)/10000000000),((901351953:ℚ)/1250000000),((97986637581:ℚ)/120100000000),((6709463671:ℚ)/7446875000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3668327563:ℚ)/10000000000),((-31000122262084855058888520112440290902583517690006249909:ℚ)/676688906640625000000000000000000000000000000000000000000),((-8693240677742632436212717:ℚ)/43320000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7153751663:ℚ)/10000000000),((3635106831:ℚ)/5000000000),((98758771619:ℚ)/121050000000),((27045747817:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((688770901:ℚ)/2000000000),((-56419033746029552965133074871043107811838703036161759939:ℚ)/1231776428906250000000000000000000000000000000000000000000),((-138896150007857079876725293:ℚ)/693120000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((7213146277:ℚ)/10000000000),((7329611341:ℚ)/10000000000),((99530901601:ℚ)/122000000000),((18169093129:ℚ)/20175000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3204359447:ℚ)/10000000000),((-519726960838792257210622294996309636665851320085655076689:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-184933915020260056719796551:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((909067573:ℚ)/1250000000),((7389008669:ℚ)/10000000000),((12537878449:ℚ)/15368750000),((54923060683:ℚ)/61000000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((736544143:ℚ)/2500000000),((-259702368087270838147504843598341448143747237673765881:ℚ)/5671992713546752929687500000000000000000000000000000000),((-184672946119718462276827431:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((3665967297:ℚ)/5000000000),((3724202827:ℚ)/5000000000),((16845858287:ℚ)/20650000000),((27669419789:ℚ)/30737500000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((665968151:ℚ)/2500000000),((-2519459699325249332633562544875823991906893147943461847:ℚ)/55035153906250000000000000000000000000000000000000000000),((-46102989985174580038954359:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((7391328311:ℚ)/10000000000),((7567198629:ℚ)/10000000000),((101847268043:ℚ)/125800000000),((56170390403:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((293595041:ℚ)/1250000000),((-543807835098992622299382671568695771643063389603162907:ℚ)/12151278759765625000000000000000000000000000000000000000),((-551669806797310982576107333:ℚ)/2772480000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((3755057449:ℚ)/5000000000),((1951195199:ℚ)/2500000000),((51695746837:ℚ)/64800000000),((14458366393:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((769752359:ℚ)/5000000000),((-2697738684085948401304364650337731267233020767770774119:ℚ)/62985600000000000000000000000000000000000000000000000000),((-12724777:ℚ)/64000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((1936921213:ℚ)/2500000000),((2426324393:ℚ)/2500000000),((26619975769:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-1780473479179273242055714662173164610590167961352089387:ℚ)/75000000000000000000000000000000000000000000000000000000),((-12724777:ℚ)/64000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((4824062411:ℚ)/5000000000),((6752952061:ℚ)/5000000000),((65592811343:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-4409215983124849237518833207209440661:ℚ)/336393216000000000000000000000000000000),((-12724777:ℚ)/64000000)⟩
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
end N11Formalization.C450Source11GroupedC30
#check @N11Formalization.C450Source11GroupedC30.bound
#print axioms N11Formalization.C450Source11GroupedC30.valid0
#print axioms N11Formalization.C450Source11GroupedC30.valid1
#print axioms N11Formalization.C450Source11GroupedC30.valid2
#print axioms N11Formalization.C450Source11GroupedC30.valid3
#print axioms N11Formalization.C450Source11GroupedC30.valid4
#print axioms N11Formalization.C450Source11GroupedC30.valid5
#print axioms N11Formalization.C450Source11GroupedC30.valid6
#print axioms N11Formalization.C450Source11GroupedC30.valid7
#print axioms N11Formalization.C450Source11GroupedC30.valid8
#print axioms N11Formalization.C450Source11GroupedC30.valid9
#print axioms N11Formalization.C450Source11GroupedC30.valid10
#print axioms N11Formalization.C450Source11GroupedC30.valid11
#print axioms N11Formalization.C450Source11GroupedC30.valid12
#print axioms N11Formalization.C450Source11GroupedC30.valid13
#print axioms N11Formalization.C450Source11GroupedC30.valid14
#print axioms N11Formalization.C450Source11GroupedC30.valid15
#print axioms N11Formalization.C450Source11GroupedC30.valid16
#print axioms N11Formalization.C450Source11GroupedC30.bound
#print axioms N11Formalization.C450Source11GroupedC30.endpoint_checks
