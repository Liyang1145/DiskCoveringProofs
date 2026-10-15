import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((1304633117:ℚ)/2000000000),((3410707787:ℚ)/5000000000),((-40819201231:ℚ)/49600000000),((-3529899351:ℚ)/5150000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2694134139:ℚ)/5000000000),((244078807519784113620318759256450248221496815638396673545133:ℚ)/4854569763840000000000000000000000000000000000000000000000000),((4514423869030580919397427:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((845114749:ℚ)/1250000000),((6940275879:ℚ)/10000000000),((-83183586427:ℚ)/103000000000),((-2295344247:ℚ)/3278125000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((592924723:ℚ)/1250000000),((17680515422802754913376535085616654236254555554477360018589003:ℚ)/375761838602187500000000000000000000000000000000000000000000000),((18086790644775704140702903:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((6879787327:ℚ)/10000000000),((1399940909:ℚ)/2000000000),((-16791231817:ℚ)/20980000000),((-18719361981:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1097158659:ℚ)/2500000000),((2355821263051031418313886090028643349539087038369668137044433:ℚ)/51733061550961610000000000000000000000000000000000000000000000),((724053846459504447963023:ℚ)/2310400000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((3469610193:ℚ)/5000000000),((1411826451:ℚ)/2000000000),((-16945743863:ℚ)/21170000000),((-3149610193:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2100412293:ℚ)/5000000000),((164627132853156549819537622855093278116177994496821719:ℚ)/3614762284062500000000000000000000000000000000000000000),((724636278986585958353983:ℚ)/2310400000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((699865241:ℚ)/1000000000),((7088845759:ℚ)/10000000000),((-85114994867:ℚ)/106800000000),((-1907595723:ℚ)/2681875000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((2002382687:ℚ)/5000000000),((19633655344597332183349192941220779101238731666256163312901107:ℚ)/438087464276253750000000000000000000000000000000000000000000000),((18123189369182510494376423:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((7028368043:ℚ)/10000000000),((3559279517:ℚ)/5000000000),((-42750633721:ℚ)/53637500000),((-19165104129:ℚ)/26937500000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3903254759:ℚ)/10000000000),((18821427261613721114657872359792843703015438955199968304107:ℚ)/419905366779874734878540039062500000000000000000000000000000),((4532618272542207796387787:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7058083427:ℚ)/10000000000),((3574136041:ℚ)/5000000000),((-42943768533:ℚ)/53875000000),((-6418083427:ℚ)/9018750000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((474897029:ℚ)/1250000000),((1140366425989978620390575669827581872712338648265159733115213:ℚ)/25438092490655364990234375000000000000000000000000000000000000),((4534439534520512740644723:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7087798567:ℚ)/10000000000),((7177984907:ℚ)/10000000000),((-9585978199:ℚ)/12025000000),((-19343395701:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((461539019:ℚ)/1250000000),((3111997626525778491880878471712866916513586423297441816707:ℚ)/69410093951503906250000000000000000000000000000000000000000),((18145044513871482024217167:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-13:ℚ)/16),((-3:ℚ)/4),((889689183:ℚ)/1250000000),((1798210309:ℚ)/2500000000),((-21616734017:ℚ)/27175000000),((-809689183:ℚ)/1134765625),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((223900797:ℚ)/625000000),((53809769057722285216631662625408443780109100988740037109479:ℚ)/1209686672874394531250000000000000000000000000000000000000000),((1134293012483794261532873:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7132370823:ℚ)/10000000000),((7207697511:ℚ)/10000000000),((-86660067643:ℚ)/108937500000),((-19477112469:ℚ)/27293750000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((705247253:ℚ)/2000000000),((28562263670969866834367132488565460219600987867518860591210489:ℚ)/642047815746062107086181640625000000000000000000000000000000000),((18152332217996588450354743:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7147228123:ℚ)/10000000000),((7222553731:ℚ)/10000000000),((-86853198503:ℚ)/109175000000),((-19521684369:ℚ)/27353125000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((693837811:ℚ)/2000000000),((41583060395554474718702147505800768765973595046338812299121661:ℚ)/934662320496684780322265625000000000000000000000000000000000000),((18155976568390034218817663:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1790521341:ℚ)/2500000000),((7237409897:ℚ)/10000000000),((-87046328661:ℚ)/109412500000),((-1630521341:ℚ)/2284375000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((3411227371:ℚ)/10000000000),((9731577033058148765559122660099453813105671875274790575022669:ℚ)/218718540912262876586914062500000000000000000000000000000000000),((18159621251162549740751847:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((3588471273:ℚ)/5000000000),((725226601:ℚ)/1000000000),((-8723945813:ℚ)/10965000000),((-9805413819:ℚ)/13735937500),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((3352303717:ℚ)/10000000000),((5666898959389605540293835914131378474391742908002071842991533:ℚ)/127353968065496690156250000000000000000000000000000000000000000),((181632662665557323398883:ℚ)/577600000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((719179967:ℚ)/1000000000),((1816780517:ℚ)/2500000000),((-21858146721:ℚ)/27471875000),((-1965539901:ℚ)/2753125000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((1646183187:ℚ)/5000000000),((223786843944958168349676046705560624074265199067871194979641:ℚ)/5028827559062776861190795898437500000000000000000000000000000),((1135431975879693998478537:ℚ)/3610000000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7206656737:ℚ)/10000000000),((1824208507:ℚ)/2500000000),((-21954710591:ℚ)/27531250000),((-19699970211:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((201959929:ℚ)/625000000),((2396102715618628935147179699240461335734866438152815190271:ℚ)/53417223000109791755676269531250000000000000000000000000000),((1135887706730373988334117:ℚ)/3610000000000000000000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3618185349:ℚ)/5000000000),((7326545777:ℚ)/10000000000),((-88205095101:ℚ)/110600000000),((-3298185349:ℚ)/4628125000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3105879727:ℚ)/10000000000),((41600331776148598451241188473950066955516989922318430914398789:ℚ)/927311230822742500000000000000000000000000000000000000000000000),((18181496331965736441534807:ℚ)/57760000000000000000000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((454130277:ℚ)/625000000),((183906433:ℚ)/250000000),((-2214783629:ℚ)/2776875000),((-1242390831:ℚ)/1742968750),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((297529209:ℚ)/1000000000),((373572374465346982103390791420552093036845435687600633229:ℚ)/8326417104136196651458740234375000000000000000000000000000),((355249818127198331641:ℚ)/1128125000000000000000)⟩
theorem valid16 : Valid source13 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7295797943:ℚ)/10000000000),((7385968659:ℚ)/10000000000),((-88977592567:ℚ)/111550000000),((-19967393829:ℚ)/28006250000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((354861307:ℚ)/1250000000),((62530041045332737101894023459173843645126602666558084102093343:ℚ)/1393569446504013443750000000000000000000000000000000000000000000),((18196086376588834939109023:ℚ)/57760000000000000000000000)⟩
theorem valid17 : Valid source13 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((7325511233:ℚ)/10000000000),((1853919949:ℚ)/2500000000),((-22340959337:ℚ)/28006250000),((-6685511233:ℚ)/9375000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((1347895901:ℚ)/5000000000),((14439694653529953855126834855274857683586688064881331:ℚ)/321777880100011825561523437500000000000000000000000000),((1137711462366084165597833:ℚ)/3610000000000000000000000)⟩
theorem valid18 : Valid source13 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((459701519:ℚ)/625000000),((1868775369:ℚ)/2500000000),((-22534079797:ℚ)/28125000000),((-1259104557:ℚ)/1772656250),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2544865977:ℚ)/10000000000),((16307642194848171515189796296546840402171689531621393677253:ℚ)/357928769016265869140625000000000000000000000000000000000000),((1138623840100428963120313:ℚ)/3610000000000000000000000)⟩
theorem valid19 : Valid source13 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((1482929961:ℚ)/2000000000),((376726119:ℚ)/500000000),((-4545439547:ℚ)/5672500000),((-369526353:ℚ)/520000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((553262641:ℚ)/2500000000),((1756784413842741040208686390441429962411624040792092043:ℚ)/38558508934003906250000000000000000000000000000000000000),((45581462060137639060813:ℚ)/144400000000000000000000)⟩
theorem valid20 : Valid source13 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((1494814893:ℚ)/2000000000),((485762413:ℚ)/625000000),((-5874911369:ℚ)/7150000000),((-1366814893:ℚ)/1970000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((113932233:ℚ)/625000000),((219522575773879747431617689039941774632954074031607501529:ℚ)/4433029275898437500000000000000000000000000000000000000000),((8088059:ℚ)/25600000)⟩
theorem valid21 : Valid source13 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-13:ℚ)/16),((-3:ℚ)/4),((1542353023:ℚ)/2000000000),((4004931923:ℚ)/5000000000),((-48544114999:ℚ)/59100000000),((-4243059069:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((142169000025162850016964511353361698325849289318489782168613:ℚ)/2880403834466250000000000000000000000000000000000000000000000),((8088059:ℚ)/25600000)⟩
theorem valid22 : Valid source13 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((63595551:ℚ)/80000000),((4242582613:ℚ)/5000000000),((-51633573969:ℚ)/61000000000),((-58475551:ℚ)/86400000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((11169115826687450957982922762224192327112681558728083851249:ℚ)/206836436250000000000000000000000000000000000000000000000000),((8088059:ℚ)/25600000)⟩
theorem valid23 : Valid source13 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((4212384957:ℚ)/5000000000),((2596521059:ℚ)/2500000000),((-394997207:ℚ)/400000000),((-11677154871:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1203419835495523676124011320154323442743373962261:ℚ)/15000000000000000000000000000000000000000000000000),((8088059:ℚ)/25600000)⟩
theorem valid24 : Valid source13 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((103257641:ℚ)/100000000),((7093581377:ℚ)/5000000000),(-1:ℚ),((-96857641:ℚ)/184000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1513538513891790681991:ℚ)/16928000000000000000000),((8088059:ℚ)/25600000)⟩
theorem valid25 : Valid source13 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet25 valid25
private theorem node1_3 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source13 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source13 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1743:ℚ)/2560) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((1743:ℚ)/2560) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source13 nn0 nn1 Qcell ((1743:ℚ)/2560) ((8753:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source13 nn0 nn1 Qcell ((8753:ℚ)/12800) ((8791:ℚ)/12800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source13 nn0 nn1 Qcell ((1743:ℚ)/2560) ((8791:ℚ)/12800) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((8791:ℚ)/12800) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((8791:ℚ)/12800) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source13 nn0 nn1 Qcell ((8791:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_join leaf13 node14_16
private theorem node17_19 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf16 node17_19
private theorem node13_19 :
    CellBound source13 nn0 nn1 Qcell ((8791:ℚ)/12800) ((45:ℚ)/64) :=
  cell_join node13_16 node16_19
private theorem node20_22 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf19 node20_22
private theorem node22_24 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node22_24 node24_26
private theorem node19_26 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node19_22 node22_26
private theorem node13_26 :
    CellBound source13 nn0 nn1 Qcell ((8791:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node13_19 node19_26
private theorem node0_26 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_26
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_26
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25]
theorem packet_count : packets.length = 26 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC04
#check @N11Formalization.C450Source13GroupedC04.bound
#print axioms N11Formalization.C450Source13GroupedC04.valid0
#print axioms N11Formalization.C450Source13GroupedC04.valid1
#print axioms N11Formalization.C450Source13GroupedC04.valid2
#print axioms N11Formalization.C450Source13GroupedC04.valid3
#print axioms N11Formalization.C450Source13GroupedC04.valid4
#print axioms N11Formalization.C450Source13GroupedC04.valid5
#print axioms N11Formalization.C450Source13GroupedC04.valid6
#print axioms N11Formalization.C450Source13GroupedC04.valid7
#print axioms N11Formalization.C450Source13GroupedC04.valid8
#print axioms N11Formalization.C450Source13GroupedC04.valid9
#print axioms N11Formalization.C450Source13GroupedC04.valid10
#print axioms N11Formalization.C450Source13GroupedC04.valid11
#print axioms N11Formalization.C450Source13GroupedC04.valid12
#print axioms N11Formalization.C450Source13GroupedC04.valid13
#print axioms N11Formalization.C450Source13GroupedC04.valid14
#print axioms N11Formalization.C450Source13GroupedC04.valid15
#print axioms N11Formalization.C450Source13GroupedC04.valid16
#print axioms N11Formalization.C450Source13GroupedC04.valid17
#print axioms N11Formalization.C450Source13GroupedC04.valid18
#print axioms N11Formalization.C450Source13GroupedC04.valid19
#print axioms N11Formalization.C450Source13GroupedC04.valid20
#print axioms N11Formalization.C450Source13GroupedC04.valid21
#print axioms N11Formalization.C450Source13GroupedC04.valid22
#print axioms N11Formalization.C450Source13GroupedC04.valid23
#print axioms N11Formalization.C450Source13GroupedC04.valid24
#print axioms N11Formalization.C450Source13GroupedC04.valid25
#print axioms N11Formalization.C450Source13GroupedC04.bound
#print axioms N11Formalization.C450Source13GroupedC04.endpoint_checks
