import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((6579838183:ℚ)/10000000000),((344301637:ℚ)/500000000),((-3275318007:ℚ)/4960000000),((-5491838183:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1048225981:ℚ)/2000000000),((285591487550942956280964325224977557555412491860561321421:ℚ)/4045474803200000000000000000000000000000000000000000000000),((251998604357015622331460741:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6818084311:ℚ)/10000000000),((875640909:ℚ)/1250000000),((-8352049999:ℚ)/12875000000),((-5730084311:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4575978151:ℚ)/10000000000),((123284954106173448392040022568712154778368486868814561260413:ℚ)/1834774602549743652343750000000000000000000000000000000000000),((251380773615365176642707749:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1734296753:ℚ)/2500000000),((176616747:ℚ)/250000000),((-1686784217:ℚ)/2622500000),((-1462296753:ℚ)/2646250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1051844999:ℚ)/2500000000),((226976149742068479114875068407314486286512240164090632947:ℚ)/3460312871291845703125000000000000000000000000000000000000),((15691680735291170242605621:ℚ)/46208000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((3498366797:ℚ)/5000000000),((3562104747:ℚ)/5000000000),((-34063152217:ℚ)/52925000000),((-2954366797:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2005618269:ℚ)/5000000000),((824991265792934921383398537060475250981994082807691813723:ℚ)/12566947003186035156250000000000000000000000000000000000000),((62727177215394928584043421:ℚ)/184832000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((705627711:ℚ)/1000000000),((7153978203:ℚ)/10000000000),((-68453760233:ℚ)/106800000000),((-596827711:ℚ)/1072750000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3805580081:ℚ)/10000000000),((71056472979620320179327205341066992653708612309943494190345851:ℚ)/1095218660690634375000000000000000000000000000000000000000000000),((2507496978493858494388949:ℚ)/7393280000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((13839937:ℚ)/19531250),((7183746193:ℚ)/10000000000),((-68781208123:ℚ)/107275000000),((-93719496:ℚ)/168359375),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((369869017:ℚ)/1000000000),((545107221114072120915486739974540452800446479397193899006803:ℚ)/8398107335597494697570800781250000000000000000000000000000000),((478114856288169774993:ℚ)/1410156250000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3557908821:ℚ)/5000000000),((3606756737:ℚ)/5000000000),((-34554324107:ℚ)/53875000000),((-3013908821:ℚ)/5411250000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((358877121:ℚ)/1000000000),((37167245983752507283544343429045099040161198295999063509354841:ℚ)/572357081039745712280273437500000000000000000000000000000000000),((173538683266306020770789:ℚ)/512000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((3572793407:ℚ)/5000000000),((3621640027:ℚ)/5000000000),((-3857560033:ℚ)/6012500000),((-3028793407:ℚ)/5435000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((695107053:ℚ)/2000000000),((1409139463880172499291984191147739438942518650719979770487:ℚ)/21690654359844970703125000000000000000000000000000000000000),((62627407106676363821485781:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((717535527:ℚ)/1000000000),((909130743:ℚ)/1250000000),((-8720438173:ℚ)/13587500000),((-608735527:ℚ)/1091750000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3358646289:ℚ)/10000000000),((607267028317488912204348436505455104367196630030910427477439:ℚ)/9343618419663073348999023437500000000000000000000000000000000),((2504291911323271946551301:ℚ)/7393280000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7205123017:ℚ)/10000000000),((456425697:ℚ)/625000000),((-4380682667:ℚ)/6823437500),((-6117123017:ℚ)/10965000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((1618854041:ℚ)/5000000000),((310441802586981411837966267475327971842515441069668800840899:ℚ)/4774599396886633479595184326171875000000000000000000000000000),((250348546749504341849475941:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7234890067:ℚ)/10000000000),((7332575687:ℚ)/10000000000),((-23472777519:ℚ)/36550000000),((-6146890067:ℚ)/11012500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3112248019:ℚ)/10000000000),((1925845077172533874817756969757714351148183600313207376714253:ℚ)/29607653603169042968750000000000000000000000000000000000000000),((250267695260534923723547741:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((1816164107:ℚ)/2500000000),((3681169779:ℚ)/5000000000),((-35372867569:ℚ)/55062500000),((-1544164107:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1490847369:ℚ)/5000000000),((486627141182410886449059776371648638064857872403691904655641:ℚ)/7478411220015370845794677734375000000000000000000000000000000),((15636664791142893883431981:ℚ)/46208000000000000000000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7294422109:ℚ)/10000000000),((7421865341:ℚ)/10000000000),((-71400518751:ℚ)/110600000000),((-6206422109:ℚ)/11155000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((569069319:ℚ)/2000000000),((156674638820569761026410519699050582385853167291821416493109:ℚ)/2378315296951562500000000000000000000000000000000000000000000),((250105370932667144042585789:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((1470790293:ℚ)/2000000000),((935173571:ℚ)/1250000000),((-9006909281:ℚ)/13943750000),((-1253190293:ℚ)/2250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((510302023:ℚ)/2000000000),((2827069687231922618559261275014452288078050477398770943:ℚ)/42889780219602584838867187500000000000000000000000000000),((9997688723007280370601581:ℚ)/29573120000000000000000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((1482695641:ℚ)/2000000000),((760042761:ℚ)/1000000000),((-7336470371:ℚ)/11250000000),((-1265095641:ℚ)/2288000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2220062679:ℚ)/10000000000),((6138653847284296224225726534672948421268936864380457428297:ℚ)/90987066650390625000000000000000000000000000000000000000000),((9991129464315818787702789:ℚ)/29573120000000000000000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((1506504819:ℚ)/2000000000),((1009561681:ℚ)/1250000000),((-9825178491:ℚ)/14300000000),((-1288904819:ℚ)/2440000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((666767481:ℚ)/5000000000),((2590954324231841356000991055584412988967066429379967885713:ℚ)/34003044521875000000000000000000000000000000000000000000000),((9977911502595134095572509:ℚ)/29573120000000000000000000)⟩
theorem valid15 : Valid source18 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((400430759:ℚ)/500000000),((2138108477:ℚ)/2500000000),((-20959193247:ℚ)/30500000000),((-346030759:ℚ)/648000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((43963608039063147584645840198582986415689313785327583508989:ℚ)/581727476953125000000000000000000000000000000000000000000000),((86308519:ℚ)/256000000)⟩
theorem valid16 : Valid source18 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8484577909:ℚ)/10000000000),((10455300373:ℚ)/10000000000),((-104768304103:ℚ)/129600000000),((-7396577909:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2125065175126668041677486055756856049714069318530276601943:ℚ)/20407334400000000000000000000000000000000000000000000000000),((86308519:ℚ)/256000000)⟩
theorem valid17 : Valid source18 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((51937561:ℚ)/50000000),((7129331127:ℚ)/5000000000),((-73302642397:ℚ)/80000000000),((-15499187:ℚ)/36800000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4572851327271762361369234535912835234893:ℚ)/33856000000000000000000000000000000000000),((86308519:ℚ)/256000000)⟩
theorem valid18 : Valid source18 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((4367:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((4367:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((4367:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source18 nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source18 nn0 nn1 Qcell ((881:ℚ)/1280) ((45:ℚ)/64) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source18 nn0 nn1 Qcell ((4367:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source18 nn0 nn1 Qcell ((4367:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC06
#check @N11Formalization.C450Source18GroupedC06.bound
#print axioms N11Formalization.C450Source18GroupedC06.valid0
#print axioms N11Formalization.C450Source18GroupedC06.valid1
#print axioms N11Formalization.C450Source18GroupedC06.valid2
#print axioms N11Formalization.C450Source18GroupedC06.valid3
#print axioms N11Formalization.C450Source18GroupedC06.valid4
#print axioms N11Formalization.C450Source18GroupedC06.valid5
#print axioms N11Formalization.C450Source18GroupedC06.valid6
#print axioms N11Formalization.C450Source18GroupedC06.valid7
#print axioms N11Formalization.C450Source18GroupedC06.valid8
#print axioms N11Formalization.C450Source18GroupedC06.valid9
#print axioms N11Formalization.C450Source18GroupedC06.valid10
#print axioms N11Formalization.C450Source18GroupedC06.valid11
#print axioms N11Formalization.C450Source18GroupedC06.valid12
#print axioms N11Formalization.C450Source18GroupedC06.valid13
#print axioms N11Formalization.C450Source18GroupedC06.valid14
#print axioms N11Formalization.C450Source18GroupedC06.valid15
#print axioms N11Formalization.C450Source18GroupedC06.valid16
#print axioms N11Formalization.C450Source18GroupedC06.valid17
#print axioms N11Formalization.C450Source18GroupedC06.valid18
#print axioms N11Formalization.C450Source18GroupedC06.bound
#print axioms N11Formalization.C450Source18GroupedC06.endpoint_checks
