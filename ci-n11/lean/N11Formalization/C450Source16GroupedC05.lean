import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((6571648929:ℚ)/10000000000),((1718813837:ℚ)/2500000000),((-4596441511:ℚ)/6200000000),((-62688138219:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5262621463:ℚ)/10000000000),((37605238175529491857084478842270676185133925816906987379:ℚ)/592598848125000000000000000000000000000000000000000000000),((4264218518759732039329571:ℚ)/12160000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6809642497:ℚ)/10000000000),((349711377:ℚ)/500000000),((-937134131:ℚ)/1287500000),((-65306067467:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4601056451:ℚ)/10000000000),((2747190493474677896624881361119024265882121370753504533:ℚ)/45869365063743591308593750000000000000000000000000000000),((4265605155268201523738979:ℚ)/12160000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((866078229:ℚ)/1250000000),((7053710637:ℚ)/10000000000),((-18921131911:ℚ)/26225000000),((-8326860519:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((846975157:ℚ)/2000000000),((5036121142047866717989454186347859394681329238048582002561:ℚ)/86507821782296142578125000000000000000000000000000000000000),((66660470155488221935971:ℚ)/190000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((6988114349:ℚ)/10000000000),((7083451459:ℚ)/10000000000),((-19010354377:ℚ)/26462500000),((-67269257839:ℚ)/106325000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((252511489:ℚ)/625000000),((1503151358100128127085146472684549727927939503391567946251679:ℚ)/26186255974970171661376953125000000000000000000000000000000000),((4266595461980922904847131:ℚ)/12160000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((1403571569:ℚ)/2000000000),((1422638361:ℚ)/2000000000),((-3819915083:ℚ)/5316250000),((-13519287259:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((1969720771:ℚ)/5000000000),((48050286030496654548182259625325375463652371109575013969:ℚ)/836813620151527862548828125000000000000000000000000000000),((170687839176363473541891:ℚ)/486400000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7047600841:ℚ)/10000000000),((3571465841:ℚ)/5000000000),((-9594397523:ℚ)/13350000000),((-67923609251:ℚ)/107275000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((767239581:ℚ)/2000000000),((3071654811059680672380744461393901259766363863814576849909:ℚ)/53477473666534881591796875000000000000000000000000000000000),((4267795303991157246029011:ℚ)/12160000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((442333959:ℚ)/625000000),((7172671097:ℚ)/10000000000),((-19278013291:ℚ)/26818750000),((-4265673549:ℚ)/6734375000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3730244721:ℚ)/10000000000),((188483654184906644118681974820460960740837386048477710111:ℚ)/3280510677967771366238594055175781250000000000000000000000),((16673411859091730166161:ℚ)/47500000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7107085361:ℚ)/10000000000),((3601205027:ℚ)/5000000000),((-9683615081:ℚ)/13468750000),((-68577938971:ℚ)/108225000000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1810671827:ℚ)/5000000000),((12849508878733199476979994688127257684624213052563720132883:ℚ)/223576984781150668859481811523437500000000000000000000000000),((4268990375328608405285251:ℚ)/12160000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7136826899:ℚ)/10000000000),((90401857:ℚ)/125000000),((-243205571:ℚ)/338203125),((-68905095889:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1754609869:ℚ)/5000000000),((145679610233246350079264999032706644300754610898015399:ℚ)/2534052408385734558105468750000000000000000000000000000),((4269586122392652019301531:ℚ)/12160000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3583283981:ℚ)/5000000000),((3630943311:ℚ)/5000000000),((-9772829933:ℚ)/13587500000),((-34616123791:ℚ)/54587500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((848388251:ℚ)/2500000000),((13432555195469805171152821466694458957584292604774187243371:ℚ)/233590460491576833724975585937500000000000000000000000000000),((56186587859807677979289:ℚ)/160000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7196308559:ℚ)/10000000000),((1822906061:ℚ)/2500000000),((-4908718183:ℚ)/6823437500),((-69559394149:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((818491851:ℚ)/2500000000),((27463601538285676182240099501460453789012253283148761089471:ℚ)/477459939688663347959518432617187500000000000000000000000000),((4270774040275102776814211:ℚ)/12160000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((3613024347:ℚ)/5000000000),((7321361433:ℚ)/10000000000),((-19724084299:ℚ)/27412500000),((-34943267817:ℚ)/55062500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3150016081:ℚ)/10000000000),((1056849541516724711317869736257344010057342632678191696301:ℚ)/18368718917407264709472656250000000000000000000000000000000),((1067841552851426864582379:ℚ)/3040000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((3627894187:ℚ)/5000000000),((3675549097:ℚ)/5000000000),((-9906647291:ℚ)/13765625000),((-35106836057:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3021161129:ℚ)/10000000000),((21519103097107297470989957619980297400860087358285747311413:ℚ)/373920561000768542289733886718750000000000000000000000000000),((1067989297718051746441739:ℚ)/3040000000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1821381901:ℚ)/2500000000),((3705285227:ℚ)/5000000000),((-1427979383:ℚ)/1975000000),((-17635200911:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1443372679:ℚ)/5000000000),((10925892121450808532409201838755518668140471408950336201:ℚ)/187227866369552612304687500000000000000000000000000000000),((267089128868129864927131:ℚ)/760000000000000000000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((367250237:ℚ)/500000000),((1867510267:ℚ)/2500000000),((-5042530801:ℚ)/6971875000),((-3559752607:ℚ)/5625000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2597742399:ℚ)/10000000000),((15647890542566163475169976567923303703469118021459279:ℚ)/268061126372516155242919921875000000000000000000000000),((10686505099463493922939:ℚ)/30400000000000000000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((7404480147:ℚ)/10000000000),((94862219:ℚ)/125000000),((-256586657:ℚ)/351562500),((-71849281617:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2273207717:ℚ)/10000000000),((4260108517976354218129089348298213720333492447517731061:ℚ)/71083645820617675781250000000000000000000000000000000000),((225133225798121306961241:ℚ)/640000000000000000000000)⟩
theorem valid15 : Valid source16 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((940428243:ℚ)/1250000000),((3913416201:ℚ)/5000000000),((-10620248603:ℚ)/14300000000),((-3048236891:ℚ)/4925000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((710369577:ℚ)/5000000000),((10726227158832619117518385394344055843701920682855641657:ℚ)/170501125996093750000000000000000000000000000000000000000),((66822957242524747144219:ℚ)/190000000000000000000000)⟩
theorem valid16 : Valid source16 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/4),((-11:ℚ)/16),((1940324653:ℚ)/2500000000),((806466513:ℚ)/1000000000),((-2195399539:ℚ)/2955000000),((-18943571183:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((1412572808857364571935375973280074442254143018360688679:ℚ)/22503154956767578125000000000000000000000000000000000000),((5626177:ℚ)/16000000)⟩
theorem valid17 : Valid source16 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((7999148013:ℚ)/10000000000),((8540271939:ℚ)/10000000000),((-23380815817:ℚ)/30500000000),((-26130209381:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((109973193723516051776032614153605264997410409970063332799:ℚ)/1615909658203125000000000000000000000000000000000000000000),((5626177:ℚ)/16000000)⟩
theorem valid18 : Valid source16 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8474785223:ℚ)/10000000000),((10442121899:ℚ)/10000000000),((-29086365697:ℚ)/32400000000),((-83622637453:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((48550063665970330961044560057590810740548807917354053:ℚ)/498225937500000000000000000000000000000000000000000000),((5626177:ℚ)/16000000)⟩
theorem valid19 : Valid source16 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((5188363913:ℚ)/5000000000),((142442923:ℚ)/100000000),(-1:ℚ),((-52272003043:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((96668023451988826035550613:ℚ)/761760000000000000000000000),((5626177:ℚ)/16000000)⟩
theorem valid20 : Valid source16 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source16 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((4367:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((4367:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((4367:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((45:ℚ)/64) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC05
#check @N11Formalization.C450Source16GroupedC05.bound
#print axioms N11Formalization.C450Source16GroupedC05.valid0
#print axioms N11Formalization.C450Source16GroupedC05.valid1
#print axioms N11Formalization.C450Source16GroupedC05.valid2
#print axioms N11Formalization.C450Source16GroupedC05.valid3
#print axioms N11Formalization.C450Source16GroupedC05.valid4
#print axioms N11Formalization.C450Source16GroupedC05.valid5
#print axioms N11Formalization.C450Source16GroupedC05.valid6
#print axioms N11Formalization.C450Source16GroupedC05.valid7
#print axioms N11Formalization.C450Source16GroupedC05.valid8
#print axioms N11Formalization.C450Source16GroupedC05.valid9
#print axioms N11Formalization.C450Source16GroupedC05.valid10
#print axioms N11Formalization.C450Source16GroupedC05.valid11
#print axioms N11Formalization.C450Source16GroupedC05.valid12
#print axioms N11Formalization.C450Source16GroupedC05.valid13
#print axioms N11Formalization.C450Source16GroupedC05.valid14
#print axioms N11Formalization.C450Source16GroupedC05.valid15
#print axioms N11Formalization.C450Source16GroupedC05.valid16
#print axioms N11Formalization.C450Source16GroupedC05.valid17
#print axioms N11Formalization.C450Source16GroupedC05.valid18
#print axioms N11Formalization.C450Source16GroupedC05.valid19
#print axioms N11Formalization.C450Source16GroupedC05.valid20
#print axioms N11Formalization.C450Source16GroupedC05.bound
#print axioms N11Formalization.C450Source16GroupedC05.endpoint_checks
