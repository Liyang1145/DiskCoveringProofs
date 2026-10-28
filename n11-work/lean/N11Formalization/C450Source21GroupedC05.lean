import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6697887131:ℚ)/10000000000),((344827737:ℚ)/500000000),((-882483211:ℚ)/1240000000),((-60876758441:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4921881689:ℚ)/10000000000),((1328369038341782520156382800360060442845982108711827966251:ℚ)/12180002684400000000000000000000000000000000000000000000000),((108870996789175692639998763:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((6817101479:ℚ)/10000000000),((7015715571:ℚ)/10000000000),((-18007146713:ℚ)/25275000000),((-62188116269:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1144726109:ℚ)/2500000000),((116887371485047331818445737906732796917449210737549683317937:ℚ)/1070601776130761718750000000000000000000000000000000000000000),((108883709065166841370182003:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((6936298599:ℚ)/10000000000),((283011613:ℚ)/400000000),((-727434839:ℚ)/1030000000),((-63499284589:ℚ)/103950000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((526280143:ℚ)/1250000000),((111648621351534847426954206911276238767270480190380646193:ℚ)/1054247643126562500000000000000000000000000000000000000000),((108830430009183524240560883:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((1748972749:ℚ)/2500000000),((1783715361:ℚ)/2500000000),((-4591146083:ℚ)/6496875000),((-16038700239:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4014075063:ℚ)/10000000000),((16658575888910202473002272953279125782811014878260851672989:ℚ)/157167693844710016250610351562500000000000000000000000000000),((6802188274526720025939483:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((3527739717:ℚ)/5000000000),((7164645671:ℚ)/10000000000),((-18453937013:ℚ)/26225000000),((-32405136887:ℚ)/52687500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((3808404783:ℚ)/10000000000),((83650532613196940454410706577329422149879032378758129014837:ℚ)/801090639542188476562500000000000000000000000000000000000000),((27201777403006691846554987:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3542636101:ℚ)/5000000000),((3597214513:ℚ)/5000000000),((-9271643539:ℚ)/13171875000),((-32568997111:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3701512017:ℚ)/10000000000),((247684566865672039780946044689108587336944393911555412294577:ℚ)/2370831949263787269592285156250000000000000000000000000000000),((27202239368483030478431083:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((355753201:ℚ)/500000000),((22575661:ℚ)/31250000),((-4015654:ℚ)/5703125),((-3273285211:ℚ)/5316250000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((448949181:ℚ)/1250000000),((4383726560040380024862147824122857374409079493938373:ℚ)/41941064579206705093383789062500000000000000000000000),((272026696049880122639683:ℚ)/577600000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((7144854901:ℚ)/10000000000),((1450798633:ℚ)/2000000000),((-3744395899:ℚ)/5316250000),((-21931134637:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((695672333:ℚ)/2000000000),((388911575066902726468667571345269380169681344765616577037:ℚ)/3719171645117901611328125000000000000000000000000000000000),((108812272461829654190991883:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3587322429:ℚ)/5000000000),((1820943493:ℚ)/2500000000),((-4702830479:ℚ)/6675000000),((-33060546719:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3361481283:ℚ)/10000000000),((2664107718928599751503186165776231171986218585863999552851:ℚ)/25465463650730895996093750000000000000000000000000000000000),((27203434902503104397247803:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((7204433903:ℚ)/10000000000),((7313553953:ℚ)/10000000000),((-18900661859:ℚ)/26818750000),((-66448772933:ℚ)/107750000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1620278467:ℚ)/5000000000),((73247180950148776343839702815414789282433690692185968334253:ℚ)/699842277966457891464233398437500000000000000000000000000000),((108815079876830025112428547:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7234222049:ℚ)/10000000000),((3671666559:ℚ)/5000000000),((-9494999677:ℚ)/13468750000),((-66776442539:ℚ)/108225000000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((623023417:ℚ)/2000000000),((1872808884109339819475694045943065970933445818492115455934653:ℚ)/17886158782492053508758544921875000000000000000000000000000000),((108816293271225207832435683:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3632004653:ℚ)/5000000000),((3686555739:ℚ)/5000000000),((-9539667217:ℚ)/13528125000),((-33552051183:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2984591809:ℚ)/10000000000),((5751285080538390266342970586957004215469631064749151857601:ℚ)/54904468848357582092285156250000000000000000000000000000000),((27204344951527364363699547:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7293795687:ℚ)/10000000000),((7432665827:ℚ)/10000000000),((-19257997481:ℚ)/27175000000),((-67431752557:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2848281381:ℚ)/10000000000),((1782296546322367035066082961166740046067228431694141825800609:ℚ)/16755733265346264648437500000000000000000000000000000000000000),((108850309846322335662583027:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((3676682933:ℚ)/5000000000),((187305427:ℚ)/250000000),((-485916281:ℚ)/685312500),((-34043512263:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1277280613:ℚ)/5000000000),((74827669883493784977657405863169042072045422164221115139:ℚ)/703053196275572204589843750000000000000000000000000000000),((27212961764191653172834187:ℚ)/57760000000000000000000000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((1853233169:ℚ)/2500000000),((7611310619:ℚ)/10000000000),((-2827704551:ℚ)/3950000000),((-17185564859:ℚ)/28125000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2223320289:ℚ)/10000000000),((13352031266587432611389678557075852016914555345754879:ℚ)/121875485229492187500000000000000000000000000000000000),((6806541564180214956584963:ℚ)/14440000000000000000000000)⟩
theorem valid14 : Valid source21 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((1883014133:ℚ)/2500000000),((7730392699:ℚ)/10000000000),((-20151178097:ℚ)/28125000000),((-17513155463:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((669077061:ℚ)/5000000000),((103870944494508966614586780537896931089616358688368889968051:ℚ)/947781944274902343750000000000000000000000000000000000000000),((18832642481410291267667:ℚ)/40000000000000000000000)⟩
theorem valid15 : Valid source21 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((7651167913:ℚ)/10000000000),((2170674393:ℚ)/2500000000),((-5752023179:ℚ)/7150000000),((-881022803:ℚ)/1600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((26246086438812760143370406519804239553640529431737327:ℚ)/175733593750000000000000000000000000000000000000000000),((1505593:ℚ)/3200000)⟩
theorem valid16 : Valid source21 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8603676041:ℚ)/10000000000),((10585990189:ℚ)/10000000000),((-28717970567:ℚ)/32400000000),((-81840436451:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2440126309152205633650854437444693086451138235887121167:ℚ)/13286025000000000000000000000000000000000000000000000000),((1505593:ℚ)/3200000)⟩
theorem valid17 : Valid source21 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((2101451739:ℚ)/2000000000),((14389851343:ℚ)/10000000000),(-1:ℚ),((-20555969129:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((242379731074904749865185603:ℚ)/975052800000000000000000000),((1505593:ℚ)/3200000)⟩
theorem valid18 : Valid source21 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source21 nn0 nn1 Qcell ((4329:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source21 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source21 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC05
#check @N11Formalization.C450Source21GroupedC05.bound
#print axioms N11Formalization.C450Source21GroupedC05.valid0
#print axioms N11Formalization.C450Source21GroupedC05.valid1
#print axioms N11Formalization.C450Source21GroupedC05.valid2
#print axioms N11Formalization.C450Source21GroupedC05.valid3
#print axioms N11Formalization.C450Source21GroupedC05.valid4
#print axioms N11Formalization.C450Source21GroupedC05.valid5
#print axioms N11Formalization.C450Source21GroupedC05.valid6
#print axioms N11Formalization.C450Source21GroupedC05.valid7
#print axioms N11Formalization.C450Source21GroupedC05.valid8
#print axioms N11Formalization.C450Source21GroupedC05.valid9
#print axioms N11Formalization.C450Source21GroupedC05.valid10
#print axioms N11Formalization.C450Source21GroupedC05.valid11
#print axioms N11Formalization.C450Source21GroupedC05.valid12
#print axioms N11Formalization.C450Source21GroupedC05.valid13
#print axioms N11Formalization.C450Source21GroupedC05.valid14
#print axioms N11Formalization.C450Source21GroupedC05.valid15
#print axioms N11Formalization.C450Source21GroupedC05.valid16
#print axioms N11Formalization.C450Source21GroupedC05.valid17
#print axioms N11Formalization.C450Source21GroupedC05.valid18
#print axioms N11Formalization.C450Source21GroupedC05.bound
#print axioms N11Formalization.C450Source21GroupedC05.endpoint_checks
