import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2959999999:ℚ)/5000000000),((644947751:ℚ)/1000000000),((3087999999:ℚ)/3560000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6778108639:ℚ)/10000000000),((-1749102496712380965639271970361342375006849319792753:ℚ)/70496900000000000000000000000000000000000000000000000),((-24025698810356815631977:ℚ)/144400000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3197499999:ℚ)/5000000000),((6686995463:ℚ)/10000000000),((9976499997:ℚ)/11060000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1427100089:ℚ)/2500000000),((-3659188807013631564420062405327959471383534254248539:ℚ)/132119044531250000000000000000000000000000000000000000),((-2386487780918555144313513:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((3316249999:ℚ)/5000000000),((1361150797:ℚ)/2000000000),((1148083333:ℚ)/1250000000),(1:ℚ),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2550482771:ℚ)/5000000000),((-4161845316695549992517523450544674363042266383577:ℚ)/143051147460937500000000000000000000000000000000000),((-95136703249548367284193:ℚ)/577600000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3375624999:ℚ)/5000000000),((216391007:ℚ)/312500000),((10510874997:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2385586917:ℚ)/5000000000),((-272045697399337721909022450726997849791556833148644131:ℚ)/9357462400000000000000000000000000000000000000000000000),((-2314773386047397230873:ℚ)/14101562500000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3434999999:ℚ)/5000000000),((6983891241:ℚ)/10000000000),((3562999999:ℚ)/3845000000),(1:ℚ),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((883769029:ℚ)/2000000000),((-1238493267440056429343956129198719599240199253451:ℚ)/41634211029052734375000000000000000000000000000000),((-7098827526909033319952411:ℚ)/43320000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3464687499:ℚ)/5000000000),((7043270193:ℚ)/10000000000),((10778062497:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1058119101:ℚ)/2500000000),((-292301768715588881423238210533778093707005247572497199:ℚ)/9831485918750000000000000000000000000000000000000000000),((-7086656635171108129751819:ℚ)/43320000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3494374999:ℚ)/5000000000),((7102649081:ℚ)/10000000000),((10867124997:ℚ)/11725000000),(1:ℚ),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((403805573:ℚ)/1000000000),((-299372559879081262898988366057836911723174139802744099:ℚ)/10074385644531250000000000000000000000000000000000000000),((-2358157055522134610301097:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3524062499:ℚ)/5000000000),((3581013953:ℚ)/5000000000),((3652062499:ℚ)/3940000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3834354797:ℚ)/10000000000),((-2838540869712163776153294095471077564632336413864893:ℚ)/95567162500000000000000000000000000000000000000000000),((-588522593411376053411193:ℚ)/3610000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3553749999:ℚ)/5000000000),((449482331:ℚ)/625000000),((11045249997:ℚ)/11867500000),(1:ℚ),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((3619803347:ℚ)/10000000000),((-313673999408747220616268117237824890717359767582417171:ℚ)/10446185617480468750000000000000000000000000000000000000),((-9187715666041945174097:ℚ)/56406250000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3568593749:ℚ)/5000000000),((7221406671:ℚ)/10000000000),((11089781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((14031357:ℚ)/40000000),((-317368453472676379319217730663556759327327323031666649:ℚ)/10572121786718750000000000000000000000000000000000000000),((-7050056497710384327663371:ℚ)/43320000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3583437499:ℚ)/5000000000),((725109603:ℚ)/1000000000),((337403409:ℚ)/362500000),(1:ℚ),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((3392339157:ℚ)/10000000000),((-571833439671386631837704990378262897818018247:ℚ)/19053906250000000000000000000000000000000000000),((-70439437197185050366979:ℚ)/433200000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3598281249:ℚ)/5000000000),((58246283:ℚ)/80000000),((11178843747:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((409116027:ℚ)/1250000000),((-81212256035237498043106146157139105236726533362212341:ℚ)/2706755626562500000000000000000000000000000000000000000),((-150140315672284203953:ℚ)/924160000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3613124999:ℚ)/5000000000),((3670082011:ℚ)/5000000000),((3741124999:ℚ)/4035000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((629832207:ℚ)/2000000000),((-9134954084730600797486941367047885882930280609306099:ℚ)/307944107226562500000000000000000000000000000000000000),((-585465293203333817091217:ℚ)/3610000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3642812499:ℚ)/5000000000),((1849885653:ℚ)/2500000000),((11312437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((721573793:ℚ)/2500000000),((-336536472351464721417535038512938924965105345906019071:ℚ)/11349050000000000000000000000000000000000000000000000000),((-438332822603590735869779:ℚ)/2707500000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((7344999997:ℚ)/10000000000),((3759149813:ℚ)/5000000000),((7600999997:ℚ)/8260000000),(1:ℚ),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((519553339:ℚ)/2000000000),((-102171835216947023109752831557233304146238013449278939:ℚ)/3522249850000000000000000000000000000000000000000000000),((-582397059414366950849713:ℚ)/3610000000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3731874999:ℚ)/5000000000),((7637056429:ℚ)/10000000000),((11579624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((474097249:ℚ)/2500000000),((-90216240132152294054339862765542571541402594597947579:ℚ)/3110727362500000000000000000000000000000000000000000000),((-80469:ℚ)/500000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3791249999:ℚ)/5000000000),((1968642359:ℚ)/2500000000),((3919249999:ℚ)/4320000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((678751219:ℚ)/10000000000),((-4673546794012117053480931512323438024984475043221731:ℚ)/167961600000000000000000000000000000000000000000000000),((-80469:ℚ)/500000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3909999999:ℚ)/5000000000),((4887325623:ℚ)/5000000000),((12113999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-26199090140351429656835369202848180134160747305554411:ℚ)/1600000000000000000000000000000000000000000000000000000),((-80469:ℚ)/500000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4859999999:ℚ)/5000000000),((13574747283:ℚ)/10000000000),((4987999999:ℚ)/7360000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1067312274039234611829404963996219:ℚ)/99672064000000000000000000000000000),((-80469:ℚ)/500000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((4747:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((4747:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((4747:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((4747:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((957:ℚ)/1280) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound eighth nn0 nn1 Qcell ((957:ℚ)/1280) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC32
#check @N11Formalization.C450EighthGroupedC32.bound
#print axioms N11Formalization.C450EighthGroupedC32.valid0
#print axioms N11Formalization.C450EighthGroupedC32.valid1
#print axioms N11Formalization.C450EighthGroupedC32.valid2
#print axioms N11Formalization.C450EighthGroupedC32.valid3
#print axioms N11Formalization.C450EighthGroupedC32.valid4
#print axioms N11Formalization.C450EighthGroupedC32.valid5
#print axioms N11Formalization.C450EighthGroupedC32.valid6
#print axioms N11Formalization.C450EighthGroupedC32.valid7
#print axioms N11Formalization.C450EighthGroupedC32.valid8
#print axioms N11Formalization.C450EighthGroupedC32.valid9
#print axioms N11Formalization.C450EighthGroupedC32.valid10
#print axioms N11Formalization.C450EighthGroupedC32.valid11
#print axioms N11Formalization.C450EighthGroupedC32.valid12
#print axioms N11Formalization.C450EighthGroupedC32.valid13
#print axioms N11Formalization.C450EighthGroupedC32.valid14
#print axioms N11Formalization.C450EighthGroupedC32.valid15
#print axioms N11Formalization.C450EighthGroupedC32.valid16
#print axioms N11Formalization.C450EighthGroupedC32.valid17
#print axioms N11Formalization.C450EighthGroupedC32.valid18
#print axioms N11Formalization.C450EighthGroupedC32.bound
#print axioms N11Formalization.C450EighthGroupedC32.endpoint_checks
