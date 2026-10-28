import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/4),((13:ℚ)/16),((5360032399:ℚ)/10000000000),((710763369:ℚ)/1250000000),((19920097197:ℚ)/25750000000),((362578187:ℚ)/400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7879960403:ℚ)/10000000000),((-97963571441461881243650231895171990693:ℚ)/341477187500000000000000000000000000000),((-28205232117952623575373:ℚ)/72200000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((5598550029:ℚ)/10000000000),((5924729117:ℚ)/10000000000),((6878550029:ℚ)/8900000000),((93021478521:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7426910871:ℚ)/10000000000),((-4937531742253689988902803736594183123719711482833661:ℚ)/17211157226562500000000000000000000000000000000000000),((-1776684321361498781890677:ℚ)/4620800000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((5836994809:ℚ)/10000000000),((3022005289:ℚ)/5000000000),((21350984427:ℚ)/27175000000),((15762022919:ℚ)/17800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3475219153:ℚ)/5000000000),((-37876761672837343028932585177995579704852070818140973483:ℚ)/125426318652343750000000000000000000000000000000000000000),((-440578216929107663861853:ℚ)/1155200000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((5956192287:ℚ)/10000000000),((308163683:ℚ)/500000000),((21708576861:ℚ)/27650000000),((4806127879:ℚ)/5435000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6701805867:ℚ)/10000000000),((-2490191515031171172243400712507378386847904698952856869:ℚ)/8257440283203125000000000000000000000000000000000000000),((-4369609639601794717077:ℚ)/11552000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((6075374307:ℚ)/10000000000),((785314913:ℚ)/1250000000),((7355374307:ℚ)/9375000000),((1744156267:ℚ)/1975000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1289029661:ℚ)/2000000000),((-516982209703250581858350482795171279842932419716284089:ℚ)/1716613769531250000000000000000000000000000000000000000),((-27082456508034807875517:ℚ)/72200000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6194541657:ℚ)/10000000000),((6342135861:ℚ)/10000000000),((22423624971:ℚ)/28362500000),((98447766193:ℚ)/112500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6179441267:ℚ)/10000000000),((-43938569282732061449922636175743986182692737107115511539:ℚ)/142598035998535156250000000000000000000000000000000000000),((-1725957266499774326897253:ℚ)/4620800000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((3127060031:ℚ)/5000000000),((6401748383:ℚ)/10000000000),((11301180093:ℚ)/14300000000),((99222728979:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1208563023:ℚ)/2000000000),((-1573789449835386553235921739766887694636378036345931:ℚ)/5112250000000000000000000000000000000000000000000000),((-1718612885753975222785677:ℚ)/4620800000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6313695073:ℚ)/10000000000),((646135697:ℚ)/1000000000),((7593695073:ℚ)/9612500000),((9999764061:ℚ)/11440000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((5903438027:ℚ)/10000000000),((-426846085574778708570939325547254339347481624862725497:ℚ)/1387807034301757812500000000000000000000000000000000000),((-17112440669552864337837:ℚ)/46208000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1593316693:ℚ)/2500000000),((3260480859:ℚ)/5000000000),((5739950079:ℚ)/7268750000),((50386251167:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1440276817:ℚ)/2500000000),((-29503556542035305999476359868107107139606508564904119:ℚ)/96010604675292968750000000000000000000000000000000000),((-425962700777895888771333:ℚ)/1155200000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((6432835243:ℚ)/10000000000),((3290281361:ℚ)/5000000000),((23138505729:ℚ)/29312500000),((50773657693:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5615595121:ℚ)/10000000000),((-1726051495400995154897979308477943058435571313163527183:ℚ)/5621866989135742187500000000000000000000000000000000000),((-424108271798638519790253:ℚ)/1155200000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6492400563:ℚ)/10000000000),((830020009:ℚ)/1250000000),((7772400563:ℚ)/9850000000),((12790260117:ℚ)/14656250000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5466644381:ℚ)/10000000000),((-458062545321787783086287792181258319747331891104907963:ℚ)/1493236914062500000000000000000000000000000000000000000),((-26390483010033531945933:ℚ)/72200000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6551962809:ℚ)/10000000000),((6699753857:ℚ)/10000000000),((23495888427:ℚ)/29787500000),((34365600047:ℚ)/39400000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1328490671:ℚ)/2500000000),((-50629752604991818230349946996533678776769157045524285923:ℚ)/165189402917480468750000000000000000000000000000000000000),((-1681524272867037431793357:ℚ)/4620800000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1322304411:ℚ)/2000000000),((3379672081:ℚ)/5000000000),((4734913233:ℚ)/6005000000),((51935737053:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1289303849:ℚ)/2500000000),((-25903278821818887771276149323629120149560852626356337:ℚ)/84586113330078125000000000000000000000000000000000000),((-418508290409126607942573:ℚ)/1155200000000000000000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((3335539187:ℚ)/5000000000),((343925733:ℚ)/500000000),((11926617561:ℚ)/15250000000),((5271034529:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4996016527:ℚ)/10000000000),((-6633206235078043840638380966892010693734704160407264841:ℚ)/22166113281250000000000000000000000000000000000000000000),((-4147443751718833677477:ℚ)/11552000000000000000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6790182501:ℚ)/10000000000),((3498836097:ℚ)/5000000000),((8070182501:ℚ)/10325000000),((53484869261:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((4658389077:ℚ)/10000000000),((-514037462889514153258983958920051947556402699194712581:ℚ)/1719848559570312500000000000000000000000000000000000000),((-410955970937819498714637:ℚ)/1155200000000000000000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((172731893:ℚ)/250000000),((7116817357:ℚ)/10000000000),((614195679:ℚ)/786250000),((108518625641:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4296412917:ℚ)/10000000000),((-885612298209053092249782183141178348057391402211:ℚ)/2966620790958404541015625000000000000000000000000),((-1628572267175609549670357:ℚ)/4620800000000000000000000)⟩
theorem valid15 : Valid source26 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source26 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((54909051:ℚ)/78125000),((3677536379:ℚ)/5000000000),((64909051:ℚ)/84375000),((55807972927:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3903287663:ℚ)/10000000000),((-39762539691829646701249279124588310094715244377:ℚ)/139045715332031250000000000000000000000000000000),((-399443718627035179235013:ℚ)/1155200000000000000000000)⟩
theorem valid16 : Valid source26 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((227077961:ℚ)/312500000),((231495491:ℚ)/250000000),((801233883:ℚ)/1250000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2973449891:ℚ)/10000000000),((-125660217135296347092402717040505317446843117670803:ℚ)/762939453125000000000000000000000000000000000000000),((-5421399:ℚ)/16000000)⟩
theorem valid17 : Valid source26 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((9170493349:ℚ)/10000000000),((6532691783:ℚ)/5000000000),((10450493349:ℚ)/18400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-141995567644092664587957951561435023:ℚ)/1557376000000000000000000000000000000),((-5421399:ℚ)/16000000)⟩
theorem valid18 : Valid source26 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source26 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC29
#check @N11Formalization.C450Source26GroupedC29.bound
#print axioms N11Formalization.C450Source26GroupedC29.valid0
#print axioms N11Formalization.C450Source26GroupedC29.valid1
#print axioms N11Formalization.C450Source26GroupedC29.valid2
#print axioms N11Formalization.C450Source26GroupedC29.valid3
#print axioms N11Formalization.C450Source26GroupedC29.valid4
#print axioms N11Formalization.C450Source26GroupedC29.valid5
#print axioms N11Formalization.C450Source26GroupedC29.valid6
#print axioms N11Formalization.C450Source26GroupedC29.valid7
#print axioms N11Formalization.C450Source26GroupedC29.valid8
#print axioms N11Formalization.C450Source26GroupedC29.valid9
#print axioms N11Formalization.C450Source26GroupedC29.valid10
#print axioms N11Formalization.C450Source26GroupedC29.valid11
#print axioms N11Formalization.C450Source26GroupedC29.valid12
#print axioms N11Formalization.C450Source26GroupedC29.valid13
#print axioms N11Formalization.C450Source26GroupedC29.valid14
#print axioms N11Formalization.C450Source26GroupedC29.valid15
#print axioms N11Formalization.C450Source26GroupedC29.valid16
#print axioms N11Formalization.C450Source26GroupedC29.valid17
#print axioms N11Formalization.C450Source26GroupedC29.valid18
#print axioms N11Formalization.C450Source26GroupedC29.bound
#print axioms N11Formalization.C450Source26GroupedC29.endpoint_checks
