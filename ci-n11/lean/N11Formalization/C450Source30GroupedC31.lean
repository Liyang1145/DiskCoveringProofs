import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/8),((15:ℚ)/16),((5099345417:ℚ)/10000000000),((5434624407:ℚ)/10000000000),((44655417919:ℚ)/51500000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((4176424217:ℚ)/5000000000),((-4669799872508493138209951220856646909:ℚ)/13261250000000000000000000000000000000),((-177369923904381066521083949:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5337331707:ℚ)/10000000000),((5672941081:ℚ)/10000000000),((46321321949:ℚ)/53400000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((79220049:ℚ)/100000000),((-280125375172042577481254644491576731:ℚ)/792100000000000000000000000000000000),((-523629121358211530903276927:ℚ)/1108992000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((2787641647:ℚ)/5000000000),((5792077901:ℚ)/10000000000),((23993491529:ℚ)/27175000000),((21088233703:ℚ)/21360000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7472068861:ℚ)/10000000000),((-980920832268050021947378122794175507527813890761637643928711:ℚ)/2665502452355200000000000000000000000000000000000000000000000),((-43300713491244840922561469:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((2847123607:ℚ)/5000000000),((5911201367:ℚ)/10000000000),((3487123607:ℚ)/3950000000),((21445604101:ℚ)/21740000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((56552961:ℚ)/78125000),((-9234134115977731385149436117871579540831028710402149465671:ℚ)/25049140950696875000000000000000000000000000000000000000000),((-42948791716076178496812909:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((2906601883:ℚ)/5000000000),((6030312161:ℚ)/10000000000),((24826213181:ℚ)/28125000000),((21802936483:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6999176559:ℚ)/10000000000),((-32112467187173114382126615358195275411818809008912978559:ℚ)/86972079600000000000000000000000000000000000000000000000),((-42597289370314447137897749:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((5932153323:ℚ)/10000000000),((3044931503:ℚ)/5000000000),((50485073261:ℚ)/56725000000),((10990794509:ℚ)/11250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6752567393:ℚ)/10000000000),((-212975449879971977931517696373636628304731200587590628293719:ℚ)/565615832519531250000000000000000000000000000000000000000000),((-509173810540955706859039967:ℚ)/1108992000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((5991625589:ℚ)/10000000000),((3074705459:ℚ)/5000000000),((50901379123:ℚ)/57200000000),((11080116377:ℚ)/11345000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3313192393:ℚ)/5000000000),((-2812147070048594903221295558503225365351518826416617217387:ℚ)/7464927329623156250000000000000000000000000000000000000000),((-169023022011737239951054261:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1512774059:ℚ)/2500000000),((6208955969:ℚ)/10000000000),((12829418413:ℚ)/14418750000),((22338867907:ℚ)/22880000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6498131347:ℚ)/10000000000),((-12513243394469903860406876718599993890581255658385562304735051:ℚ)/33201829933958400000000000000000000000000000000000000000000000),((-10520116006199172209315221:ℚ)/23104000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6110565303:ℚ)/10000000000),((6268498231:ℚ)/10000000000),((51733957121:ℚ)/58150000000),((22517494693:ℚ)/23070000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((636767917:ℚ)/1000000000),((-57979314719164186914550292046809895695667681760488557458021:ℚ)/153772422969630250000000000000000000000000000000000000000000),((-502863314628217985132416007:ℚ)/1108992000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((617003283:ℚ)/1000000000),((632803777:ℚ)/1000000000),((745003283:ℚ)/837500000),((2269611331:ℚ)/2326000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((77936093:ℚ)/125000000),((-33294446078475115635462337463209620700535041730823592049:ℚ)/88267080578537500000000000000000000000000000000000000000),((-263559106608430448477813:ℚ)/583680000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((3114749427:ℚ)/5000000000),((3193787327:ℚ)/5000000000),((26283245989:ℚ)/29550000000),((11437361981:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((6099600527:ℚ)/10000000000),((-110651094265327272467013624893374937304823396480983336976357:ℚ)/293232624358959960937500000000000000000000000000000000000000),((-124665632383072403525017967:ℚ)/277248000000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1572240853:ℚ)/2500000000),((3223554473:ℚ)/5000000000),((13245685971:ℚ)/14893750000),((11526663419:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5961645701:ℚ)/10000000000),((-819450790114420373015378370021875583646729334932438784993707:ℚ)/2170784777799850000000000000000000000000000000000000000000000),((-10345083191615846790156469:ℚ)/23104000000000000000000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3174213269:ℚ)/5000000000),((6506640709:ℚ)/10000000000),((26699492883:ℚ)/30025000000),((23231922127:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5820830383:ℚ)/10000000000),((-2879251183229393564394582390094184188076693567194870165704477:ℚ)/7624619518642455859375000000000000000000000000000000000000000),((-41205557599087411691421301:ℚ)/92416000000000000000000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6407888267:ℚ)/10000000000),((6566170001:ℚ)/10000000000),((53815217869:ℚ)/60525000000),((23410510003:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((709617347:ℚ)/1250000000),((-21308633501733579100519382811280228728595861058176067844989857:ℚ)/56408700641382450000000000000000000000000000000000000000000000),((-164123540445003480660519349:ℚ)/369664000000000000000000000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((808418579:ℚ)/1250000000),((82821211:ℚ)/125000000),((6778930053:ℚ)/7625000000),((294863633:ℚ)/302625000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2764863881:ℚ)/5000000000),((-3006905852416952261318605868201853492595008912731803:ℚ)/7957361270764160156250000000000000000000000000000000),((-2553519695115691866689381:ℚ)/5776000000000000000000000)⟩
theorem valid14 : Valid source30 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source30 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1305361533:ℚ)/2000000000),((6744743627:ℚ)/10000000000),((1561361533:ℚ)/1770000000),((23946230881:ℚ)/24400000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1075784357:ℚ)/2000000000),((-88158920746274484494783820574894441557111780839088013932857:ℚ)/237036258300000000000000000000000000000000000000000000000000),((-19438550797396151072114447:ℚ)/44359680000000000000000000)⟩
theorem valid15 : Valid source30 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((25959851:ℚ)/39062500),((6863781377:ℚ)/10000000000),((216718957:ℚ)/245703125),((24303344131:ℚ)/24780000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((5065220411:ℚ)/10000000000),((-506600945260839039551380276001506167203920357180404365443:ℚ)/1360885207913916015625000000000000000000000000000000000000),((-313659106086310210835473:ℚ)/722000000000000000000000)⟩
theorem valid16 : Valid source30 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source30 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((3382315539:ℚ)/5000000000),((3550915739:ℚ)/5000000000),((28156208773:ℚ)/32400000000),((12508747217:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1183172529:ℚ)/2500000000),((-577784400398104696018489062596543089461191662179177393793:ℚ)/1600743703950000000000000000000000000000000000000000000000),((-118291490310601377339985583:ℚ)/277248000000000000000000000)⟩
theorem valid17 : Valid source30 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source30 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((7002435489:ℚ)/10000000000),((4026871153:ℚ)/5000000000),((57977048423:ℚ)/72400000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((99799449:ℚ)/250000000),((-8440345330191043738328382086658555131:ℚ)/26208800000000000000000000000000000000),((-455128300993225122683343383:ℚ)/1108992000000000000000000000)⟩
theorem valid18 : Valid source30 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((3976746549:ℚ)/5000000000),((4502644591:ℚ)/5000000000),((32317225843:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-2611919221971176352617279089357088851:ℚ)/8000000000000000000000000000000000000),((-10538749:ℚ)/25600000)⟩
theorem valid19 : Valid source30 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source30 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((556521843:ℚ)/625000000),((6404671857:ℚ)/5000000000),((4455652901:ℚ)/6900000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1838098831634532437709653:ℚ)/7935000000000000000000000),((-10538749:ℚ)/25600000)⟩
theorem valid20 : Valid source30 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source30 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source30 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source30 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source30 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source30 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC31
#check @N11Formalization.C450Source30GroupedC31.bound
#print axioms N11Formalization.C450Source30GroupedC31.valid0
#print axioms N11Formalization.C450Source30GroupedC31.valid1
#print axioms N11Formalization.C450Source30GroupedC31.valid2
#print axioms N11Formalization.C450Source30GroupedC31.valid3
#print axioms N11Formalization.C450Source30GroupedC31.valid4
#print axioms N11Formalization.C450Source30GroupedC31.valid5
#print axioms N11Formalization.C450Source30GroupedC31.valid6
#print axioms N11Formalization.C450Source30GroupedC31.valid7
#print axioms N11Formalization.C450Source30GroupedC31.valid8
#print axioms N11Formalization.C450Source30GroupedC31.valid9
#print axioms N11Formalization.C450Source30GroupedC31.valid10
#print axioms N11Formalization.C450Source30GroupedC31.valid11
#print axioms N11Formalization.C450Source30GroupedC31.valid12
#print axioms N11Formalization.C450Source30GroupedC31.valid13
#print axioms N11Formalization.C450Source30GroupedC31.valid14
#print axioms N11Formalization.C450Source30GroupedC31.valid15
#print axioms N11Formalization.C450Source30GroupedC31.valid16
#print axioms N11Formalization.C450Source30GroupedC31.valid17
#print axioms N11Formalization.C450Source30GroupedC31.valid18
#print axioms N11Formalization.C450Source30GroupedC31.valid19
#print axioms N11Formalization.C450Source30GroupedC31.valid20
#print axioms N11Formalization.C450Source30GroupedC31.bound
#print axioms N11Formalization.C450Source30GroupedC31.endpoint_checks
