import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((258469373:ℚ)/400000000),((6757500003:ℚ)/10000000000),(-1:ℚ),((-734448119:ℚ)/824000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((346486053:ℚ)/625000000),((44900364820816836669160267546489:ℚ)/1697440000000000000000000000000000),((1281296527012532308136607:ℚ)/4731699200000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((6699262577:ℚ)/10000000000),((3438125001:ℚ)/5000000000),(-1:ℚ),((-19073787731:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((491805051:ℚ)/1000000000),((13839442265671688420336845345763813:ℚ)/550200500000000000000000000000000000),((802450248584785453434704007:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1363605187:ℚ)/2000000000),((6935625003:ℚ)/10000000000),(-1:ℚ),((-3886015561:ℚ)/4234000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((572019001:ℚ)/1250000000),((1099229412012477143285744808476671:ℚ)/44816890000000000000000000000000000),((32130615730587614804343327:ℚ)/118292480000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((3438703717:ℚ)/5000000000),((3497500001:ℚ)/5000000000),(-1:ℚ),((-9804111151:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((879199699:ℚ)/2000000000),((3493650312262523062250182500806959:ℚ)/142578000000000000000000000000000000),((201042673180561105825598287:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((6936788817:ℚ)/10000000000),((7054375003:ℚ)/10000000000),(-1:ℚ),((-19786366451:ℚ)/21550000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((526082827:ℚ)/1250000000),((666142672177068505186589107229869:ℚ)/27211083984375000000000000000000000),((805075189722123237913740487:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((874521261:ℚ)/1250000000),((3542031251:ℚ)/5000000000),(-1:ℚ),((-2495563783:ℚ)/2705625000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((160525403:ℚ)/400000000),((544673315788080640717958459916509:ℚ)/22524328125000000000000000000000000),((12585624270553690174718143:ℚ)/46208000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((3512930341:ℚ)/5000000000),((3556875001:ℚ)/5000000000),(-1:ℚ),((-10026791023:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((488989559:ℚ)/1250000000),((21421135264460479240889927042917967:ℚ)/886176750000000000000000000000000000),((201482874906564422966825423:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((5644441:ℚ)/8000000),((7143437503:ℚ)/10000000000),(-1:ℚ),((-16114123:ℚ)/17468000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((476018819:ℚ)/1250000000),((8640333819034715088351458120501:ℚ)/357575418750000000000000000000000),((516085021010643918199:ℚ)/1892679680000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((708524179:ℚ)/1000000000),((1789570313:ℚ)/2500000000),(-1:ℚ),((-2023172537:ℚ)/2188250000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((3701622631:ℚ)/10000000000),((230012179006326920658269037401189:ℚ)/9576876125000000000000000000000000),((8065845249373910370525503:ℚ)/29573120000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((142001741:ℚ)/200000000),((3586562501:ℚ)/5000000000),(-1:ℚ),((-405525223:ℚ)/438600000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((729449477:ℚ)/2000000000),((339668589747216566790591212047:ℚ)/14144850000000000000000000000000),((322724008894567137693823:ℚ)/1182924800000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((444683269:ℚ)/625000000),((449248047:ℚ)/625000000),(-1:ℚ),((-1270049807:ℚ)/1373593750),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((3592086493:ℚ)/10000000000),((28992411526327183314901236326292969:ℚ)/1207526265625000000000000000000000000),((3152482302260875915170063:ℚ)/11552000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((7129777551:ℚ)/10000000000),((3601406251:ℚ)/5000000000),(-1:ℚ),((-20365332653:ℚ)/22025000000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((3536103131:ℚ)/10000000000),((14556633260970384294538684222877677:ℚ)/606375781250000000000000000000000000),((807260866366174014104526983:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((893077849:ℚ)/1250000000),((7217656253:ℚ)/10000000000),(-1:ℚ),((-2551233547:ℚ)/2759062500),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((3479257531:ℚ)/10000000000),((9744798348941664695257514671758283:ℚ)/405996046875000000000000000000000000),((12616972081466216912110583:ℚ)/46208000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((7159468027:ℚ)/10000000000),((7232500003:ℚ)/10000000000),(-1:ℚ),((-20454404081:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1710753327:ℚ)/5000000000),((524210661373869746216476186991791:ℚ)/21843500000000000000000000000000000),((807711509888224480563803407:ℚ)/2957312000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1434862651:ℚ)/2000000000),((905917969:ℚ)/1250000000),(-1:ℚ),((-4099787953:ℚ)/4433500000),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((1681401901:ℚ)/5000000000),((1179098897937215571752970508246933:ℚ)/49139805625000000000000000000000000),((32317470255641110133533583:ℚ)/118292480000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1797289619:ℚ)/2500000000),((3631093751:ℚ)/5000000000),(-1:ℚ),((-5135868857:ℚ)/5553750000),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((412887269:ℚ)/1250000000),((2466618435150102140429896303132171:ℚ)/102813796875000000000000000000000000),((50510122047245678196870463:ℚ)/184832000000000000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((1801000923:ℚ)/2500000000),((1819257813:ℚ)/2500000000),(-1:ℚ),((-5147002769:ℚ)/5565625000),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((648466847:ℚ)/2000000000),((2286280252188915685844923151049229:ℚ)/95311328125000000000000000000000000),((50524193685182430853997007:ℚ)/184832000000000000000000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7218848901:ℚ)/10000000000),((3645937501:ℚ)/5000000000),(-1:ℚ),((-20632546703:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((397556417:ℚ)/1250000000),((7461034645440883183629778353921243:ℚ)/311085062500000000000000000000000000),((808612195015329080920813583:ℚ)/2957312000000000000000000000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2231:ℚ)/3200),((8943:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((904211763:ℚ)/1250000000),((7306718753:ℚ)/10000000000),(-1:ℚ),((-2584635289:ℚ)/2794687500),((961640533:ℚ)/1000000000),((9622019977:ℚ)/10000000000),((555749933:ℚ)/2000000000),((623476549:ℚ)/2000000000),((5993381414025932964181253258307181:ℚ)/249928903125000000000000000000000000),((12638081889506122433708927:ℚ)/46208000000000000000000000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((8943:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((8943:ℚ)/12800),((4481:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((72485393:ℚ)/100000000),((7321562503:ℚ)/10000000000),(-1:ℚ),((-207216179:ℚ)/224050000),((1922169193:ℚ)/2000000000),((1923281067:ℚ)/2000000000),((349868089:ℚ)/1250000000),((3053054917:ℚ)/10000000000),((7221587686013137018081748618779:ℚ)/301190415000000000000000000000000),((80906223667020581348167:ℚ)/295731200000000000000000)⟩
theorem valid19 : Valid ninth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound ninth nn0 nn1 Qcell ((8943:ℚ)/12800) ((4481:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),(-1:ℚ),((-15:ℚ)/16),((7263384491:ℚ)/10000000000),((3675625001:ℚ)/5000000000),(-1:ℚ),((-20766153473:ℚ)/22500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((746846607:ℚ)/2500000000),((635604212962384589228391880890533:ℚ)/26367187500000000000000000000000000),((809536647677535192261987823:ℚ)/2957312000000000000000000000)⟩
theorem valid20 : Valid ninth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3646537427:ℚ)/5000000000),((3690468751:ℚ)/5000000000),(-1:ℚ),((-10427612281:ℚ)/11297500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1425827423:ℚ)/5000000000),((1922335368799511244176710293653547:ℚ)/79770941406250000000000000000000000),((202496597094903495098294207:ℚ)/739328000000000000000000000)⟩
theorem valid21 : Valid ninth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7322765193:ℚ)/10000000000),((7410625003:ℚ)/10000000000),(-1:ℚ),((-20944295579:ℚ)/22690000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((135466277:ℚ)/500000000),((1550341154812253024594603241096543:ℚ)/64354512500000000000000000000000000),((810435928475114814749500567:ℚ)/2957312000000000000000000000)⟩
theorem valid22 : Valid ninth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((1838113877:ℚ)/2500000000),((7470000003:ℚ)/10000000000),(-1:ℚ),((-5258341631:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((39989021:ℚ)/156250000),((153151977581195301259959648306523:ℚ)/6292000000000000000000000000000000),((50711512425682007746010607:ℚ)/184832000000000000000000000)⟩
theorem valid23 : Valid ninth packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1852959017:ℚ)/2500000000),((7588750003:ℚ)/10000000000),(-1:ℚ),((-5302877051:ℚ)/5815000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2229854491:ℚ)/10000000000),((6294875688038928641258307705046421:ℚ)/253606687500000000000000000000000000),((50830008600774158017004887:ℚ)/184832000000000000000000000)⟩
theorem valid24 : Valid ninth packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((1882649229:ℚ)/2500000000),((3853750001:ℚ)/5000000000),(-1:ℚ),((-5391947687:ℚ)/5910000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1352473111:ℚ)/10000000000),((1081778567317941889326078190935661:ℚ)/43660125000000000000000000000000000),((50829201824248070569608703:ℚ)/184832000000000000000000000)⟩
theorem valid25 : Valid ninth packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(-1:ℚ),((-15:ℚ)/16),((1529871483:ℚ)/2000000000),((3972500001:ℚ)/5000000000),(-1:ℚ),((-4384814449:ℚ)/4880000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((4581382532643226322552991888624617:ℚ)/178608000000000000000000000000000000),((281560841:ℚ)/1024000000)⟩
theorem valid26 : Valid ninth packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((7886877431:ℚ)/10000000000),((8420000003:ℚ)/10000000000),(-1:ℚ),((-22636632293:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((45628643752288649411114694198422069:ℚ)/1679616000000000000000000000000000000),((281560841:ℚ)/1024000000)⟩
theorem valid27 : Valid ninth packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((4180956971:ℚ)/5000000000),((5160000001:ℚ)/5000000000),(-1:ℚ),((-12030870913:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((64735273704002014632275382612036653:ℚ)/1920000000000000000000000000000000000),((281560841:ℚ)/1024000000)⟩
theorem valid28 : Valid ninth packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((10262025299:ℚ)/10000000000),((14120000003:ℚ)/10000000000),(-1:ℚ),((-29762075897:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((18837129060247278718887851:ℚ)/487526400000000000000000000),((281560841:ℚ)/1024000000)⟩
theorem valid29 : Valid ninth packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet29 valid29
private theorem node1_3 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound ninth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound ninth nn0 nn1 Qcell ((2117:ℚ)/3200) ((1087:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((8753:ℚ)/12800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound ninth nn0 nn1 Qcell ((8753:ℚ)/12800) ((8791:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((8791:ℚ)/12800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound ninth nn0 nn1 Qcell ((8791:ℚ)/12800) ((8829:ℚ)/12800) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound ninth nn0 nn1 Qcell ((8829:ℚ)/12800) ((8867:ℚ)/12800) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound ninth nn0 nn1 Qcell ((8791:ℚ)/12800) ((8867:ℚ)/12800) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((8867:ℚ)/12800) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((8867:ℚ)/12800) :=
  cell_join node0_7 node7_15
private theorem node16_18 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound ninth nn0 nn1 Qcell ((8867:ℚ)/12800) ((2231:ℚ)/3200) :=
  cell_join leaf15 node16_18
private theorem node18_20 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_join leaf18 leaf19
private theorem node20_22 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf20 leaf21
private theorem node18_22 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join node18_20 node20_22
private theorem node15_22 :
    CellBound ninth nn0 nn1 Qcell ((8867:ℚ)/12800) ((4519:ℚ)/6400) :=
  cell_join node15_18 node18_22
private theorem node22_24 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join node22_24 node24_26
private theorem node26_28 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf26 leaf27
private theorem node28_30 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf28 leaf29
private theorem node26_30 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node26_28 node28_30
private theorem node22_30 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node22_26 node26_30
private theorem node15_30 :
    CellBound ninth nn0 nn1 Qcell ((8867:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node15_22 node22_30
private theorem node0_30 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_30
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_30
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29]
theorem packet_count : packets.length = 30 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC01
#check @N11Formalization.C450NinthGroupedC01.bound
#print axioms N11Formalization.C450NinthGroupedC01.valid0
#print axioms N11Formalization.C450NinthGroupedC01.valid1
#print axioms N11Formalization.C450NinthGroupedC01.valid2
#print axioms N11Formalization.C450NinthGroupedC01.valid3
#print axioms N11Formalization.C450NinthGroupedC01.valid4
#print axioms N11Formalization.C450NinthGroupedC01.valid5
#print axioms N11Formalization.C450NinthGroupedC01.valid6
#print axioms N11Formalization.C450NinthGroupedC01.valid7
#print axioms N11Formalization.C450NinthGroupedC01.valid8
#print axioms N11Formalization.C450NinthGroupedC01.valid9
#print axioms N11Formalization.C450NinthGroupedC01.valid10
#print axioms N11Formalization.C450NinthGroupedC01.valid11
#print axioms N11Formalization.C450NinthGroupedC01.valid12
#print axioms N11Formalization.C450NinthGroupedC01.valid13
#print axioms N11Formalization.C450NinthGroupedC01.valid14
#print axioms N11Formalization.C450NinthGroupedC01.valid15
#print axioms N11Formalization.C450NinthGroupedC01.valid16
#print axioms N11Formalization.C450NinthGroupedC01.valid17
#print axioms N11Formalization.C450NinthGroupedC01.valid18
#print axioms N11Formalization.C450NinthGroupedC01.valid19
#print axioms N11Formalization.C450NinthGroupedC01.valid20
#print axioms N11Formalization.C450NinthGroupedC01.valid21
#print axioms N11Formalization.C450NinthGroupedC01.valid22
#print axioms N11Formalization.C450NinthGroupedC01.valid23
#print axioms N11Formalization.C450NinthGroupedC01.valid24
#print axioms N11Formalization.C450NinthGroupedC01.valid25
#print axioms N11Formalization.C450NinthGroupedC01.valid26
#print axioms N11Formalization.C450NinthGroupedC01.valid27
#print axioms N11Formalization.C450NinthGroupedC01.valid28
#print axioms N11Formalization.C450NinthGroupedC01.valid29
#print axioms N11Formalization.C450NinthGroupedC01.bound
#print axioms N11Formalization.C450NinthGroupedC01.endpoint_checks
