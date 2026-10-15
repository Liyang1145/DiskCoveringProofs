import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((6512549917:ℚ)/10000000000),((1702748743:ℚ)/2500000000),((-4820246229:ℚ)/4960000000),((-42387849419:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((338464237:ℚ)/625000000),((1102953450728242143970773595982417850528579:ℚ)/25284217520000000000000000000000000000000000),((292564185914535253720692519:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((3375070171:ℚ)/5000000000),((3464886119:ℚ)/5000000000),((-9818658357:ℚ)/10300000000),((-22025491197:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2387176159:ℚ)/5000000000),((1171806844566465425287114524862030836098116088083698937093:ℚ)/29356393640795898437500000000000000000000000000000000000000),((73323394312116468385890711:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((858616637:ℚ)/1250000000),((873645063:ℚ)/1250000000),((-2476935189:ℚ)/2622500000),((-5610316459:ℚ)/6615625000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4422126689:ℚ)/10000000000),((19297016415384873143214112896012185536089040271347814684981:ℚ)/505205679208609472656250000000000000000000000000000000000000),((4588408718918488108604999:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((3464164449:ℚ)/5000000000),((3524274267:ℚ)/5000000000),((-9996822801:ℚ)/10585000000),((-22649151143:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((16546197:ℚ)/39062500),((5042159217964368164731224683983371316847995631335788049601:ℚ)/132103746897491601562500000000000000000000000000000000000000),((220518647081364353962348813:ℚ)/693120000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((6987724329:ℚ)/10000000000),((3539121231:ℚ)/5000000000),((-3347121231:ℚ)/3560000000),((-45714070303:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((4041489051:ℚ)/10000000000),((193919095694071455449640780908087956429100064806496712678079:ℚ)/5192147724755600000000000000000000000000000000000000000000000),((882621314867155066678575133:ℚ)/2772480000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((1754355477:ℚ)/2500000000),((3553968167:ℚ)/5000000000),((-10085904501:ℚ)/10727500000),((-11480488339:ℚ)/13468750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((157637427:ℚ)/400000000),((53518679905824470577630145222550757180442126422483644172189:ℚ)/1433276985275305761718750000000000000000000000000000000000000),((55198207504716440770935877:ℚ)/173280000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7047119399:ℚ)/10000000000),((7137630149:ℚ)/10000000000),((-20260890447:ℚ)/21550000000),((-15376611931:ℚ)/18037500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((479736259:ℚ)/1250000000),((4862198378189014262253165416726503348038671083323797217745607:ℚ)/130243033552155468750000000000000000000000000000000000000000000),((15503882634093132074350309:ℚ)/48640000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3538408401:ℚ)/5000000000),((1788119259:ℚ)/2500000000),((-564039753:ℚ)/601250000),((-23168858807:ℚ)/27115625000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((3732145343:ℚ)/10000000000),((3777534482979474895486253213039497244308419861343662989737:ℚ)/102278530682823352050781250000000000000000000000000000000000),((220998655676405993761490413:ℚ)/693120000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7091665471:ℚ)/10000000000),((716732391:ℚ)/1000000000),((-2034997173:ℚ)/2169250000),((-46441658297:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((3678188141:ℚ)/10000000000),((173995508132486545090238204930121083944145413213572061597:ℚ)/4711377908696204083251953125000000000000000000000000000000),((294756534932290737080915311:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((7106514119:ℚ)/10000000000),((718217077:ℚ)/1000000000),((-2039451231:ℚ)/2174000000),((-15515199611:ℚ)/18156250000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((3623464697:ℚ)/10000000000),((7147419827600012121559192956846104487905508407796115393:ℚ)/193549867659903125000000000000000000000000000000000000000),((294848194369209311444404031:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1424272549:ℚ)/2000000000),((449813601:ℚ)/625000000),((-425813601:ℚ)/453906250),((-9329907843:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((3567939697:ℚ)/10000000000),((7349871932077725873317240340240865013978449598431474511:ℚ)/199047561925242468714714050292968750000000000000000000000),((11797594101840264587746071:ℚ)/36966400000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((142724227:ℚ)/200000000),((7211864449:ℚ)/10000000000),((-20483593347:ℚ)/21835000000),((-935069589:ℚ)/1094125000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((702315011:ℚ)/2000000000),((16732096349001627084709454567335691489656773788655720098989257:ℚ)/453169609937786560156250000000000000000000000000000000000000000),((118012603787544532001959:ℚ)/369664000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3575529967:ℚ)/5000000000),((1806677817:ℚ)/2500000000),((-5132033451:ℚ)/5470625000),((-7809569923:ℚ)/9137500000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((690865921:ℚ)/2000000000),((807499048208956046564768725111618953359324199845455780939:ℚ)/21871854091226287658691406250000000000000000000000000000000),((73780791282891743875520719:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7165908497:ℚ)/10000000000),((3620779037:ℚ)/5000000000),((-3428779037:ℚ)/3655000000),((-46961359479:ℚ)/54943750000),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((424519843:ℚ)/1250000000),((20247606547376685325905216594060546475378464641212431495279:ℚ)/548466701401794531250000000000000000000000000000000000000000),((295214819540339995102105039:ℚ)/924160000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((7180757039:ℚ)/10000000000),((7256404867:ℚ)/10000000000),((-20617214601:ℚ)/21977500000),((-47065299273:ℚ)/55062500000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((3337014013:ℚ)/10000000000),((475222844378781065306149985188611482527269313537030297762249:ℚ)/12873798551200708764648437500000000000000000000000000000000000),((15542445931325545779727189:ℚ)/48640000000000000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((179890139:ℚ)/250000000),((7271251647:ℚ)/10000000000),((-20661754941:ℚ)/22025000000),((-393076991:ℚ)/459843750),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((3276842613:ℚ)/10000000000),((7116148029292629495825671984798375441788653144916876357652903:ℚ)/192791125213652636718750000000000000000000000000000000000000000),((184623827872567550401891:ℚ)/577600000000000000000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((7210454061:ℚ)/10000000000),((3643049207:ℚ)/5000000000),((-3451049207:ℚ)/3678750000),((-47273178427:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3215586841:ℚ)/10000000000),((501716628374223215681122852563323350949903186039082182321:ℚ)/13593555518071398925781250000000000000000000000000000000000),((886469325729224145954324373:ℚ)/2772480000000000000000000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3612651271:ℚ)/5000000000),((456309073:ℚ)/625000000),((-185275317:ℚ)/197500000),((-23688558897:ℚ)/27709375000),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((3153183431:ℚ)/10000000000),((139710103517086011564941258549575928658656586056196383717:ℚ)/3785600097741308593750000000000000000000000000000000000000),((73895356159022504409790911:ℚ)/231040000000000000000000000)⟩
theorem valid17 : Valid source11 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3620075501:ℚ)/5000000000),((7315791909:ℚ)/10000000000),((-20795375727:ℚ)/22167500000),((-23740528507:ℚ)/27768750000),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3089562779:ℚ)/10000000000),((16531886875873209532206912094477611839839782676245345192861781:ℚ)/447983006968488293847656250000000000000000000000000000000000000),((73918268193799320697401671:ℚ)/231040000000000000000000000)⟩
theorem valid18 : Valid source11 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source11 nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3627499721:ℚ)/5000000000),((7345485353:ℚ)/10000000000),((-6961485353:ℚ)/7405000000),((-23792498047:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1512324001:ℚ)/5000000000),((470850572901084370888998281950716663953937216089426376643273:ℚ)/12631483132793282031250000000000000000000000000000000000000000),((73964234871495924422761311:ℚ)/231040000000000000000000000)⟩
theorem valid19 : Valid source11 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3642348131:ℚ)/5000000000),((3687589373:ℚ)/5000000000),((-10486768119:ℚ)/11155000000),((-23896436917:ℚ)/28006250000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((2890585309:ℚ)/10000000000),((282260907288736132138067690757441362434858616472938130329257:ℚ)/7573746991869638281250000000000000000000000000000000000000000),((74010057336358415064741031:ℚ)/231040000000000000000000000)⟩
theorem valid20 : Valid source11 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-15:ℚ)/16),((-7:ℚ)/8),((7314393003:ℚ)/10000000000),((740487209:ℚ)/1000000000),((-2106261627:ℚ)/2240500000),((-48000751021:ℚ)/56250000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((171886659:ℚ)/625000000),((707181115284712506981861678613620475856162868479729:ℚ)/18979231635210937500000000000000000000000000000000000),((888670542623307730495582117:ℚ)/2772480000000000000000000000)⟩
theorem valid21 : Valid source11 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3672044833:ℚ)/5000000000),((746425863:ℚ)/1000000000),((-236008621:ℚ)/250000000),((-24104313831:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1301212891:ℚ)/5000000000),((19100188281108434274404936042034878850922190525992841021:ℚ)/502769628906250000000000000000000000000000000000000000000),((74147808140671732190953519:ℚ)/231040000000000000000000000)⟩
theorem valid22 : Valid source11 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((7403482761:ℚ)/10000000000),((7523644979:ℚ)/10000000000),((-21418934937:ℚ)/22690000000),((-48624379327:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((569755887:ℚ)/2500000000),((2267356342115670542666386439009701542272119944765726643657:ℚ)/59719418636985250000000000000000000000000000000000000000000),((890873330153790845349412573:ℚ)/2772480000000000000000000000)⟩
theorem valid23 : Valid source11 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1865718889:ℚ)/2500000000),((47765107:ℚ)/62500000),((-136095321:ℚ)/143000000),((-12260032223:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((380496613:ℚ)/2000000000),((243354926895711753659875267793632103120782504407833081:ℚ)/6179987090285937500000000000000000000000000000000000000),((51494062046175877076231:ℚ)/160000000000000000000000)⟩
theorem valid24 : Valid source11 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((7581660273:ℚ)/10000000000),((7761188549:ℚ)/10000000000),((-22131565647:ℚ)/23260000000),((-49871621911:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((138970303:ℚ)/2000000000),((269928264568008368509258868245511724397171358082272310082823:ℚ)/6867902466373837500000000000000000000000000000000000000000000),((892274833880480945947416877:ℚ)/2772480000000000000000000000)⟩
theorem valid25 : Valid source11 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-15:ℚ)/16),((-7:ℚ)/8),((3850221937:ℚ)/5000000000),((1599745881:ℚ)/2000000000),((-1522945881:ℚ)/1576000000),((-25351553559:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((3819484229139686534884775436363376628694361630528431009:ℚ)/91034985385600000000000000000000000000000000000000000000),((5149311:ℚ)/16000000)⟩
theorem valid26 : Valid source11 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((3969003967:ℚ)/5000000000),((8473803927:ℚ)/10000000000),((-24269411781:ℚ)/24400000000),((-8727675923:ℚ)/10800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((775855192955413521731231744757982668462936945261558902141:ℚ)/16546914900000000000000000000000000000000000000000000000000),((5149311:ℚ)/16000000)⟩
theorem valid27 : Valid source11 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((420656239:ℚ)/500000000),((5187015603:ℚ)/5000000000),(-1:ℚ),((-2784593673:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((835748175931322632189409322440123:ℚ)/15000000000000000000000000000000000),((5149311:ℚ)/16000000)⟩
theorem valid28 : Valid source11 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((2578370283:ℚ)/2500000000),((1771787249:ℚ)/1250000000),(-1:ℚ),((-17248591981:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5923997406383655703276939:ℚ)/95220000000000000000000000),((5149311:ℚ)/16000000)⟩
theorem valid29 : Valid source11 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet29 valid29
private theorem node1_3 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source11 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source11 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source11 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4329:ℚ)/6400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((4329:ℚ)/6400) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source11 nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((881:ℚ)/1280) :=
  cell_join node0_7 node7_15
private theorem node16_18 :
    CellBound source11 nn0 nn1 Qcell ((8829:ℚ)/12800) ((8867:ℚ)/12800) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((8867:ℚ)/12800) :=
  cell_join leaf15 node16_18
private theorem node18_20 :
    CellBound source11 nn0 nn1 Qcell ((8867:ℚ)/12800) ((2231:ℚ)/3200) :=
  cell_join leaf18 leaf19
private theorem node20_22 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf20 leaf21
private theorem node18_22 :
    CellBound source11 nn0 nn1 Qcell ((8867:ℚ)/12800) ((45:ℚ)/64) :=
  cell_join node18_20 node20_22
private theorem node15_22 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((45:ℚ)/64) :=
  cell_join node15_18 node18_22
private theorem node22_24 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node22_24 node24_26
private theorem node26_28 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf26 leaf27
private theorem node28_30 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf28 leaf29
private theorem node26_30 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node26_28 node28_30
private theorem node22_30 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node22_26 node26_30
private theorem node15_30 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node15_22 node22_30
private theorem node0_30 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_30
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_30
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29]
theorem packet_count : packets.length = 30 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC02
#check @N11Formalization.C450Source11GroupedC02.bound
#print axioms N11Formalization.C450Source11GroupedC02.valid0
#print axioms N11Formalization.C450Source11GroupedC02.valid1
#print axioms N11Formalization.C450Source11GroupedC02.valid2
#print axioms N11Formalization.C450Source11GroupedC02.valid3
#print axioms N11Formalization.C450Source11GroupedC02.valid4
#print axioms N11Formalization.C450Source11GroupedC02.valid5
#print axioms N11Formalization.C450Source11GroupedC02.valid6
#print axioms N11Formalization.C450Source11GroupedC02.valid7
#print axioms N11Formalization.C450Source11GroupedC02.valid8
#print axioms N11Formalization.C450Source11GroupedC02.valid9
#print axioms N11Formalization.C450Source11GroupedC02.valid10
#print axioms N11Formalization.C450Source11GroupedC02.valid11
#print axioms N11Formalization.C450Source11GroupedC02.valid12
#print axioms N11Formalization.C450Source11GroupedC02.valid13
#print axioms N11Formalization.C450Source11GroupedC02.valid14
#print axioms N11Formalization.C450Source11GroupedC02.valid15
#print axioms N11Formalization.C450Source11GroupedC02.valid16
#print axioms N11Formalization.C450Source11GroupedC02.valid17
#print axioms N11Formalization.C450Source11GroupedC02.valid18
#print axioms N11Formalization.C450Source11GroupedC02.valid19
#print axioms N11Formalization.C450Source11GroupedC02.valid20
#print axioms N11Formalization.C450Source11GroupedC02.valid21
#print axioms N11Formalization.C450Source11GroupedC02.valid22
#print axioms N11Formalization.C450Source11GroupedC02.valid23
#print axioms N11Formalization.C450Source11GroupedC02.valid24
#print axioms N11Formalization.C450Source11GroupedC02.valid25
#print axioms N11Formalization.C450Source11GroupedC02.valid26
#print axioms N11Formalization.C450Source11GroupedC02.valid27
#print axioms N11Formalization.C450Source11GroupedC02.valid28
#print axioms N11Formalization.C450Source11GroupedC02.valid29
#print axioms N11Formalization.C450Source11GroupedC02.bound
#print axioms N11Formalization.C450Source11GroupedC02.endpoint_checks
