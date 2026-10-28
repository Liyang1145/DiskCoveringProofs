import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((13:ℚ)/16),((7:ℚ)/8),((5342556103:ℚ)/10000000000),((2833809919:ℚ)/5000000000),((84173229339:ℚ)/103000000000),((23676669433:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7912344161:ℚ)/10000000000),((-453722584556181256473631736326160740467:ℚ)/1365908750000000000000000000000000000000),((-258618749129819324417441397:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((5580701381:ℚ)/10000000000),((5905918767:ℚ)/10000000000),((87269117953:ℚ)/106800000000),((49021431369:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7461572711:ℚ)/10000000000),((-1096904205210744014346671534269338875041221226458540923:ℚ)/3304542187500000000000000000000000000000000000000000000),((-3035316336866800495838548159:ℚ)/8871936000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1163760113:ℚ)/2000000000),((6025047183:ℚ)/10000000000),((18072881469:ℚ)/21740000000),((16618443427:ℚ)/17800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((279509457:ℚ)/400000000),((-22376938198723615232426451590762424898529692431981436031:ℚ)/64218275150000000000000000000000000000000000000000000000),((-3001113582469839514737599359:ℚ)/8871936000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((5937834391:ℚ)/10000000000),((3072081269:ℚ)/5000000000),((13130263869:ℚ)/15800000000),((25344568883:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((269624007:ℚ)/400000000),((-536101652382391318494786947069543095665493267981442919:ℚ)/1540746875000000000000000000000000000000000000000000000),((-247234303700831219176913997:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((6056858431:ℚ)/10000000000),((6263265497:ℚ)/10000000000),((10384351067:ℚ)/12500000000),((51522858479:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3242794907:ℚ)/5000000000),((-4241611820492070169794915385254763724599880317043663073:ℚ)/12207031250000000000000000000000000000000000000000000000),((-977470121393936371029107493:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((192996037:ℚ)/312500000),((6322812523:ℚ)/10000000000),((2968948481:ℚ)/3545312500),((51939687661:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1555428443:ℚ)/2500000000),((-98915200480793528001030759010687234113847692748606231:ℚ)/278511789059638977050781250000000000000000000000000000),((-971724141434688571631867533:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((779422153:ℚ)/1250000000),((6382356681:ℚ)/10000000000),((1088407999:ℚ)/1300000000),((52356496767:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((38038031:ℚ)/62500000),((-14992205392471773868159556366135062003849538180633:ℚ)/42250000000000000000000000000000000000000000000000),((-2897909593744030928873109391:ℚ)/8871936000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3147439557:ℚ)/5000000000),((161047451:ℚ)/250000000),((48276714241:ℚ)/57675000000),((9226099:ℚ)/10000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((594776829:ℚ)/1000000000),((-106279728544856582317778719765458824649799733297724589699:ℚ)/299766319409179687500000000000000000000000000000000000000),((-600129553368602460204077:ℚ)/1848320000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6354378907:ℚ)/10000000000),((650143667:ℚ)/1000000000),((97326925791:ℚ)/116300000000),((5319005669:ℚ)/5767500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((232262749:ℚ)/400000000),((-139310774395122974112876302953429347725777749833320587469:ℚ)/393259436750000000000000000000000000000000000000000000000),((-9544363982790174191544253:ℚ)/29573120000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((1282775331:ℚ)/2000000000),((3280486319:ℚ)/5000000000),((19620079303:ℚ)/23450000000),((26803404233:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2831133797:ℚ)/5000000000),((-1018832836814888742986571911315142178910122068350944771:ℚ)/2878395898437500000000000000000000000000000000000000000),((-237164299479808336511387797:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((809171551:ℚ)/1250000000),((827563251:ℚ)/1250000000),((12359230163:ℚ)/14775000000),((6752942757:ℚ)/7328125000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5514618383:ℚ)/10000000000),((-594140487244378994681420294005322481778446265260709139:ℚ)/1679891528320312500000000000000000000000000000000000000),((-44197016214082790391931831:ℚ)/138624000000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3266433107:ℚ)/5000000000),((6680036843:ℚ)/10000000000),((49823630391:ℚ)/59575000000),((54440257901:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5363341497:ℚ)/10000000000),((-467029146702978170093994857346849488015543771328682256109:ℚ)/1321515223339843750000000000000000000000000000000000000000),((-937073837206497947934117773:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((164808953:ℚ)/250000000),((6739565203:ℚ)/10000000000),((2510516389:ℚ)/3002500000),((54856956421:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((651014711:ℚ)/1250000000),((-3733816539026807567244200297753507557082026178127471:ℚ)/10573264166259765625000000000000000000000000000000000),((-931269667077710947833360893:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((1662962043:ℚ)/2500000000),((3399545573:ℚ)/5000000000),((25298506559:ℚ)/30262500000),((27636819011:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1262144927:ℚ)/2500000000),((-754628702736297042339585559076264669424467509717869941:ℚ)/2138500744628906250000000000000000000000000000000000000),((-231364291062133075440633133:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((1677834103:ℚ)/2500000000),((685861473:ℚ)/1000000000),((25491843339:ℚ)/30500000000),((1856343437:ℚ)/2017500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2442150779:ℚ)/5000000000),((-62530398562858517288562143670408439785702180591210297681:ℚ)/177328906250000000000000000000000000000000000000000000000),((-27589089722599556108592799:ℚ)/88719360000000000000000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6770822883:ℚ)/10000000000),((6977655037:ℚ)/10000000000),((14677242497:ℚ)/17700000000),((56523585259:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2357392213:ℚ)/5000000000),((-996634071288956208530557464502863147677004176427162289:ℚ)/2888142187500000000000000000000000000000000000000000000),((-907969614638783762575325213:ℚ)/2957312000000000000000000000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1722447671:ℚ)/2500000000),((443542909:ℚ)/625000000),((26071819723:ℚ)/31450000000),((3584800363:ℚ)/3871875000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2178777527:ℚ)/5000000000),((-65454608616237250129947472462864708514782421132358297:ℚ)/189863730621337890625000000000000000000000000000000000),((-3501052755281639733335837:ℚ)/11552000000000000000000000)⟩
theorem valid16 : Valid source25 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source25 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((7008751889:ℚ)/10000000000),((916840589:ℚ)/1250000000),((105833774557:ℚ)/129600000000),((7377884123:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1985270337:ℚ)/5000000000),((-18526220483199537601405102860274649981225941356578645261:ℚ)/55987200000000000000000000000000000000000000000000000000),((-13637015059209210439341117:ℚ)/46208000000000000000000000)⟩
theorem valid17 : Valid source25 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((905831959:ℚ)/1250000000),((1657318821:ℚ)/2000000000),((13615815467:ℚ)/18100000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((153064481:ℚ)/500000000),((-610800447220053768676555873736881244208968071252842673:ℚ)/2316305078125000000000000000000000000000000000000000000),((-293081019:ℚ)/1024000000)⟩
theorem valid18 : Valid source25 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((8198058417:ℚ)/10000000000),((4619053729:ℚ)/5000000000),((121294759421:ℚ)/160000000000),((36173376103:ℚ)/36200000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-1727319683778232382866492046640883561075360100500232483391:ℚ)/6400000000000000000000000000000000000000000000000000000000),((-293081019:ℚ)/1024000000)⟩
theorem valid19 : Valid source25 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source25 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((9149194159:ℚ)/10000000000),((13042074189:ℚ)/10000000000),((44553174689:ℚ)/73600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-12028204091414824077278644218458320217:ℚ)/99672064000000000000000000000000000000),((-293081019:ℚ)/1024000000)⟩
theorem valid20 : Valid source25 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source25 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source25 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source25 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source25 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC30
#check @N11Formalization.C450Source25GroupedC30.bound
#print axioms N11Formalization.C450Source25GroupedC30.valid0
#print axioms N11Formalization.C450Source25GroupedC30.valid1
#print axioms N11Formalization.C450Source25GroupedC30.valid2
#print axioms N11Formalization.C450Source25GroupedC30.valid3
#print axioms N11Formalization.C450Source25GroupedC30.valid4
#print axioms N11Formalization.C450Source25GroupedC30.valid5
#print axioms N11Formalization.C450Source25GroupedC30.valid6
#print axioms N11Formalization.C450Source25GroupedC30.valid7
#print axioms N11Formalization.C450Source25GroupedC30.valid8
#print axioms N11Formalization.C450Source25GroupedC30.valid9
#print axioms N11Formalization.C450Source25GroupedC30.valid10
#print axioms N11Formalization.C450Source25GroupedC30.valid11
#print axioms N11Formalization.C450Source25GroupedC30.valid12
#print axioms N11Formalization.C450Source25GroupedC30.valid13
#print axioms N11Formalization.C450Source25GroupedC30.valid14
#print axioms N11Formalization.C450Source25GroupedC30.valid15
#print axioms N11Formalization.C450Source25GroupedC30.valid16
#print axioms N11Formalization.C450Source25GroupedC30.valid17
#print axioms N11Formalization.C450Source25GroupedC30.valid18
#print axioms N11Formalization.C450Source25GroupedC30.valid19
#print axioms N11Formalization.C450Source25GroupedC30.valid20
#print axioms N11Formalization.C450Source25GroupedC30.bound
#print axioms N11Formalization.C450Source25GroupedC30.endpoint_checks
