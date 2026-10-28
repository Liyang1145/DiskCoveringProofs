import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((101878029:ℚ)/156250000),((3409152543:ℚ)/5000000000),((-9267457629:ℚ)/12400000000),((-990658319:ℚ)/1609375000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5395883669:ℚ)/10000000000),((6509423456391417547020901677586103151206213477616061445619:ℚ)/126421087600000000000000000000000000000000000000000000000000),((2117713052979506565477:ℚ)/7050781250000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6758056177:ℚ)/10000000000),((6937221861:ℚ)/10000000000),((-18891665583:ℚ)/25750000000),((-66018617947:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4751635371:ℚ)/10000000000),((1429115875671699111653082926733889390257856165606874697064017:ℚ)/29356393640795898437500000000000000000000000000000000000000000),((69437008463175814162730229:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((6876977473:ℚ)/10000000000),((3498338999:ℚ)/5000000000),((-9535016997:ℚ)/13112500000),((-67326752203:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4397327649:ℚ)/10000000000),((40971194375391629888134266439340642129069724012582202444491:ℚ)/865078217822961425781250000000000000000000000000000000000000),((69458820768310772964580629:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((693643581:ℚ)/1000000000),((7056132689:ℚ)/10000000000),((-19248398067:ℚ)/26462500000),((-6798079391:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2104899687:ℚ)/5000000000),((148849056993815848711745762221196181017257024722990520389:ℚ)/3141736750796508789062500000000000000000000000000000000000),((694821519971514009737661:ℚ)/2310400000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((6995892661:ℚ)/10000000000),((1417171901:ℚ)/2000000000),((-1289171901:ℚ)/1780000000),((-68634819271:ℚ)/107275000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((250879341:ℚ)/625000000),((474024793434570615520256736374269311474399402595564718139:ℚ)/10140913524913281250000000000000000000000000000000000000000),((69493024156540548277911021:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((3512810271:ℚ)/5000000000),((7115585973:ℚ)/10000000000),((-19426757919:ℚ)/26818750000),((-34480912981:ℚ)/53875000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((782549017:ℚ)/2000000000),((4090151639975405330264978019208064932864514551934253928161:ℚ)/87480284745807236433029174804687500000000000000000000000000),((17376169422362406365555541:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3527674033:ℚ)/5000000000),((3572656049:ℚ)/5000000000),((-9757968147:ℚ)/13468750000),((-888318317:ℚ)/1387500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3808869787:ℚ)/10000000000),((183315065495665430369133802945074865823974328326086683111:ℚ)/3919824409925937652587890625000000000000000000000000000000),((17379081932964001580815989:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3542537619:ℚ)/5000000000),((1435007577:ℚ)/2000000000),((-1307007577:ℚ)/1803750000),((-34807913809:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1851114177:ℚ)/5000000000),((18263169890950841391075461159900022492654688103186890073:ℚ)/390431778477209472656250000000000000000000000000000000000),((17381993571459833670783261:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7114802063:ℚ)/10000000000),((3602381669:ℚ)/5000000000),((-9847145007:ℚ)/13587500000),((-69942822693:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3592573953:ℚ)/10000000000),((874324654678441650191159669760231655768378169007153859899633:ℚ)/18687236839326146697998046875000000000000000000000000000000000),((69539617353058341262714869:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((223266517:ℚ)/312500000),((3617244231:ℚ)/5000000000),((-9891732693:ℚ)/13646875000),((-731977229:ℚ)/1142187500),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((695924247:ℚ)/2000000000),((5841535204264327886837178109884599677238044660604705363979:ℚ)/124826128023179960250854492187500000000000000000000000000000),((67921149351213301549689:ℚ)/225625000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((224195459:ℚ)/312500000),((363210663:ℚ)/500000000),((-331210663:ℚ)/456875000),((-2206150049:ℚ)/3441406250),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((336303733:ℚ)/1000000000),((5413481582831014143479519840305885971592331120614865257:ℚ)/115654896887379074096679687500000000000000000000000000000),((3575395406803727042199:ℚ)/11875000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7203980497:ℚ)/10000000000),((3646968869:ℚ)/5000000000),((-9980906607:ℚ)/13765625000),((-70923785467:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3242430033:ℚ)/10000000000),((58352462736635758985082293036919582687565021403362261268997:ℚ)/1246401870002561807632446289062500000000000000000000000000000),((69574525653022360859049909:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7233705977:ℚ)/10000000000),((3661830949:ℚ)/5000000000),((-10025492847:ℚ)/13825000000),((-23750255249:ℚ)/37025000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((311733181:ℚ)/1000000000),((424045527237840666277412187189269143190940660643266508235097:ℚ)/9055773738503344726562500000000000000000000000000000000000000),((69586154791175491988919429:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7263431131:ℚ)/10000000000),((3676692873:ℚ)/5000000000),((-3356692873:ℚ)/4628125000),((-71577742441:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((746794477:ℚ)/2500000000),((9027023531333209610362245966002187560540292181581895458187:ℚ)/192741136669819366931915283203125000000000000000000000000000),((3663041076409120973449119:ℚ)/12160000000000000000000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((1823288991:ℚ)/2500000000),((185320813:ℚ)/250000000),((-507962439:ℚ)/697187500),((-17976178901:ℚ)/28125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2851275449:ℚ)/10000000000),((84808138080036608649751312234364072928037750076411:ℚ)/1787074175816774368286132812500000000000000000000000),((4351365398461253285444181:ℚ)/14440000000000000000000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7352604683:ℚ)/10000000000),((7472278089:ℚ)/10000000000),((-6832278089:ℚ)/9375000000),((-72558651513:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((639630463:ℚ)/2500000000),((3146205820190588323005760190028382610259225271382828593159:ℚ)/66283105373382568359375000000000000000000000000000000000000),((69645080071270095165601389:ℚ)/231040000000000000000000000)⟩
theorem valid15 : Valid source14 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((1853013041:ℚ)/2500000000),((1882930621:ℚ)/2500000000),((-5168791863:ℚ)/7090625000),((-18303143451:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2228568361:ℚ)/10000000000),((2163073546653903822126270289172185693828066866002817163917:ℚ)/45562300595844459533691406250000000000000000000000000000000),((4354268742988080987473781:ℚ)/14440000000000000000000000)⟩
theorem valid16 : Valid source14 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((186787461:ℚ)/250000000),((7769488891:ℚ)/10000000000),((-21388466673:ℚ)/28600000000),((-1846662071:ℚ)/2955000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1841519121:ℚ)/10000000000),((72339871846052262109482707352287288013944489444776948002727:ℚ)/1418569368287500000000000000000000000000000000000000000000000),((120663442407037718661:ℚ)/400000000000000000000)⟩
theorem valid17 : Valid source14 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/4),((-11:ℚ)/16),((1541854413:ℚ)/2000000000),((320289547:ℚ)/400000000),((-294689547:ℚ)/394000000),((-15296398543:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((72368368907501094326611659561610143610976392092270117:ℚ)/1422421646650000000000000000000000000000000000000000000),((4826283:ℚ)/16000000)⟩
theorem valid18 : Valid source14 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((3973514309:ℚ)/5000000000),((8482694239:ℚ)/10000000000),((-23528082717:ℚ)/30500000000),((-39548657399:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((21329635024012762117553109974979446024265175699465263215929:ℚ)/387818317968750000000000000000000000000000000000000000000000),((4826283:ℚ)/16000000)⟩
theorem valid19 : Valid source14 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((4211248261:ℚ)/5000000000),((2596020813:ℚ)/2500000000),((-2436020813:ℚ)/2700000000),((-42163730871:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1795034693591602045028587080573446082520114413824969:ℚ)/23066015625000000000000000000000000000000000000000000),((4826283:ℚ)/16000000)⟩
theorem valid20 : Valid source14 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((10323923151:ℚ)/10000000000),((2837142621:ℚ)/2000000000),(-1:ℚ),((-105243154661:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((50598944919203666346088121:ℚ)/507840000000000000000000000),((4826283:ℚ)/16000000)⟩
theorem valid21 : Valid source14 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((881:ℚ)/1280) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((881:ℚ)/1280) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((2269:ℚ)/3200) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC05
#check @N11Formalization.C450Source14GroupedC05.bound
#print axioms N11Formalization.C450Source14GroupedC05.valid0
#print axioms N11Formalization.C450Source14GroupedC05.valid1
#print axioms N11Formalization.C450Source14GroupedC05.valid2
#print axioms N11Formalization.C450Source14GroupedC05.valid3
#print axioms N11Formalization.C450Source14GroupedC05.valid4
#print axioms N11Formalization.C450Source14GroupedC05.valid5
#print axioms N11Formalization.C450Source14GroupedC05.valid6
#print axioms N11Formalization.C450Source14GroupedC05.valid7
#print axioms N11Formalization.C450Source14GroupedC05.valid8
#print axioms N11Formalization.C450Source14GroupedC05.valid9
#print axioms N11Formalization.C450Source14GroupedC05.valid10
#print axioms N11Formalization.C450Source14GroupedC05.valid11
#print axioms N11Formalization.C450Source14GroupedC05.valid12
#print axioms N11Formalization.C450Source14GroupedC05.valid13
#print axioms N11Formalization.C450Source14GroupedC05.valid14
#print axioms N11Formalization.C450Source14GroupedC05.valid15
#print axioms N11Formalization.C450Source14GroupedC05.valid16
#print axioms N11Formalization.C450Source14GroupedC05.valid17
#print axioms N11Formalization.C450Source14GroupedC05.valid18
#print axioms N11Formalization.C450Source14GroupedC05.valid19
#print axioms N11Formalization.C450Source14GroupedC05.valid20
#print axioms N11Formalization.C450Source14GroupedC05.valid21
#print axioms N11Formalization.C450Source14GroupedC05.bound
#print axioms N11Formalization.C450Source14GroupedC05.endpoint_checks
