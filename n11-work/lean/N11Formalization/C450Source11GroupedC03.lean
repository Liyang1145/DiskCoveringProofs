import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((811118383:ℚ)/1250000000),((3392293361:ℚ)/5000000000),((-22306053527:ℚ)/24800000000),((-9744538979:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2737689701:ℚ)/5000000000),((1042897335867849512814489594045402307056509:ℚ)/25284217520000000000000000000000000000000000),((527271281482167708096332013:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3363289107:ℚ)/5000000000),((862923689:ℚ)/1250000000),((-5680465823:ℚ)/6437500000),((-40522758391:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4841388837:ℚ)/10000000000),((274152866368747244118150011427526668410851489209368515967:ℚ)/7167088291209936141967773437500000000000000000000000000000),((33022009353035528291829213:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((6845390223:ℚ)/10000000000),((1740697549:ℚ)/2500000000),((-11464882843:ℚ)/13112500000),((-82590072899:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4493969611:ℚ)/10000000000),((2327340826212649229641241838428226641714454988307812226567643:ℚ)/63150709901076184082031250000000000000000000000000000000000000),((132223219551340717855439253:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((26971857:ℚ)/39062500),((3511095211:ℚ)/5000000000),((-23137666477:ℚ)/26462500000),((-325634141:ℚ)/417187500),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2155271839:ℚ)/5000000000),((76050630781400028370630741775780145858081781575702291812933:ℚ)/2064121045273306274414062500000000000000000000000000000000000),((529433803217213049502016613:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((870525003:ℚ)/1250000000),((110185787:ℚ)/156250000),((-726300509:ℚ)/834375000),((-1502403577:ℚ)/1915625000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((2059746043:ℚ)/5000000000),((148054232864854487434862030715360381547468427210548285247:ℚ)/4092663801010322570800781250000000000000000000000000000000),((517289393980083500839557:ℚ)/1805000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((109279721:ℚ)/156250000),((1770397551:ℚ)/2500000000),((-11672782857:ℚ)/13409375000),((-1320636373:ℚ)/1683593750),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2010383773:ℚ)/5000000000),((101266279338977094450663663355608743943613192006166023720377:ℚ)/2799369111865831565856933593750000000000000000000000000000000),((397481193605279628882759559:ℚ)/1386240000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3511802067:ℚ)/5000000000),((7111289931:ℚ)/10000000000),((-46899029517:ℚ)/53875000000),((-42453426871:ℚ)/54112500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1959848113:ℚ)/5000000000),((662538472139631880144800521765546107103291825860356390200720453:ℚ)/18315426593271862792968750000000000000000000000000000000000000000),((6362946712080851667179077999:ℚ)/22179840000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((1763326499:ℚ)/2500000000),((446311847:ℚ)/625000000),((-2944182929:ℚ)/3382031250),((-21323244487:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3816091191:ℚ)/10000000000),((31001028006450339749776717557720953063029833725404043141297:ℚ)/857024443429831632971763610839843750000000000000000000000000),((8289316297835818222047677:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((7083007733:ℚ)/10000000000),((7155839323:ℚ)/10000000000),((-47210875261:ℚ)/54350000000),((-85679100529:ℚ)/108937500000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((3709739679:ℚ)/10000000000),((975746428867334074990342871813810854271604801425296514606867:ℚ)/27217950139673876953125000000000000000000000000000000000000000),((2122606413479841613344274437:ℚ)/7393280000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1419571711:ℚ)/2000000000),((7170689067:ℚ)/10000000000),((-15771607823:ℚ)/18156250000),((-17174432243:ℚ)/21835000000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((1827729587:ℚ)/5000000000),((913384685631838364206508966946033898690812595657637156515049:ℚ)/25478087926431035995483398437500000000000000000000000000000000),((6369443711649200105836296751:ℚ)/22179840000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7112709347:ℚ)/10000000000),((3592769393:ℚ)/5000000000),((-23709385751:ℚ)/27293750000),((-86065221511:ℚ)/109412500000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((3600397821:ℚ)/10000000000),((31730932228091257599304945795970596524866330173399604005876909:ℚ)/885096894409739375305175781250000000000000000000000000000000000),((530922360882077637465890797:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7127560107:ℚ)/10000000000),((3600194239:ℚ)/5000000000),((-23761359673:ℚ)/27353125000),((-86258281391:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((3544519177:ℚ)/10000000000),((882134977064774009620856473337922000477761055176417571679417:ℚ)/24605835852629573616027832031250000000000000000000000000000000),((531057758085593426655910413:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7142410837:ℚ)/10000000000),((1443047629:ℚ)/2000000000),((-9525333403:ℚ)/10965000000),((-86451340881:ℚ)/109887500000),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((3487783891:ℚ)/10000000000),((530903563556913015318816044865452789885759712746924925172361:ℚ)/14808600937848452343750000000000000000000000000000000000000000),((84990906815917420080173973:ℚ)/295731200000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((7157261537:ℚ)/10000000000),((3615043893:ℚ)/5000000000),((-23865307251:ℚ)/27471875000),((-86644399981:ℚ)/110125000000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((214384337:ℚ)/625000000),((901452474226218667861444711134246421410606001682867338124299:ℚ)/25144137795313884305953979492187500000000000000000000000000000),((1593985768243697102986785391:ℚ)/5544960000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((448257013:ℚ)/625000000),((3622468701:ℚ)/5000000000),((-23917280907:ℚ)/27531250000),((-1809113723:ℚ)/2299218750),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((3371569499:ℚ)/10000000000),((13499802888520663924285847989099504887901758293319680235937249:ℚ)/376545166432915306091308593750000000000000000000000000000000000),((1594392070619681535359497759:ℚ)/5544960000000000000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((224592589:ℚ)/312500000),((7259786993:ℚ)/10000000000),((-47938508951:ℚ)/55181250000),((-2719703657:ℚ)/3456250000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3311993991:ℚ)/10000000000),((1644830853051432574545097681234278940042391626175767767353297:ℚ)/45878249873490971374511718750000000000000000000000000000000000),((2126397879901619927487951597:ℚ)/7393280000000000000000000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((3600906729:ℚ)/5000000000),((3637318279:ℚ)/5000000000),((-24021227953:ℚ)/27650000000),((-43611787477:ℚ)/55418750000),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((325136807:ℚ)/1000000000),((53203357695902950995680505833313234444089038196952664630381999:ℚ)/1483955238314592968750000000000000000000000000000000000000000000),((531734928711913295534584573:ℚ)/1848320000000000000000000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((180416601:ℚ)/250000000),((7289486099:ℚ)/10000000000),((-48146402693:ℚ)/55418750000),((-2185415813:ℚ)/2776875000),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((637926353:ℚ)/2000000000),((83653127197737872216499562323698052928705449953594650491869733:ℚ)/2333244827960876530456542968750000000000000000000000000000000000),((2127481599070398382484650453:ℚ)/7393280000000000000000000000)⟩
theorem valid17 : Valid source11 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source11 nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((7231514591:ℚ)/10000000000),((1460867123:ℚ)/2000000000),((-9650069861:ℚ)/11107500000),((-87609689683:ℚ)/111312500000),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((195419953:ℚ)/625000000),((974051926247754227290216085239121798206891843322324400497269:ℚ)/27167947042449026074218750000000000000000000000000000000000000),((85120941301324625755410837:ℚ)/295731200000000000000000000)⟩
theorem valid18 : Valid source11 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet source11 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3623182557:ℚ)/5000000000),((7319185107:ℚ)/10000000000),((-48354295749:ℚ)/55656250000),((-43901373241:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((61251159:ℚ)/200000000),((3004481291783462157476550698093346661728373936242303460767989:ℚ)/83799418957037630677223205566406250000000000000000000000000000),((6385696545816155266259739391:ℚ)/22179840000000000000000000000)⟩
theorem valid19 : Valid source11 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source11 nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((907651951:ℚ)/1250000000),((459305251:ℚ)/625000000),((-3035136757:ℚ)/3485937500),((-10999475363:ℚ)/14003125000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((599413521:ℚ)/2000000000),((8358918350726665212592970187339538952442363784256449911839:ℚ)/231132415523365426063537597656250000000000000000000000000000),((8318943861203466061616053:ℚ)/28880000000000000000000000)⟩
theorem valid20 : Valid source11 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((7290916511:ℚ)/10000000000),((737858283:ℚ)/1000000000),((-4877007981:ℚ)/5601250000),((-88381914643:ℚ)/112500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((1430866329:ℚ)/5000000000),((10724382719584521009822518084974736790543631386022583:ℚ)/296550494300170898437500000000000000000000000000000000),((63922018164076599259935151:ℚ)/221798400000000000000000000)⟩
theorem valid21 : Valid source11 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((73206173:ℚ)/100000000),((7437980173:ℚ)/10000000000),((-49185861211:ℚ)/56250000000),((-887680249:ℚ)/1134500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2719865549:ℚ)/10000000000),((210617546683884922836699743963660438296301316780380610365704091:ℚ)/5726860304260253906250000000000000000000000000000000000000000000),((2132903150879076296774089237:ℚ)/7393280000000000000000000000)⟩
theorem valid22 : Valid source11 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((461251159:ℚ)/625000000),((937172143:ℚ)/1250000000),((-6200205001:ℚ)/7090625000),((-5596265067:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2411872767:ℚ)/10000000000),((67008685179918023172073792243594127687764620860050737369:ℚ)/1822492023833778381347656250000000000000000000000000000000),((33360517996539766887962797:ℚ)/115520000000000000000000000)⟩
theorem valid23 : Valid source11 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7439419351:ℚ)/10000000000),((7616170009:ℚ)/10000000000),((-50433190063:ℚ)/57200000000),((-90312451563:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2059313523:ℚ)/10000000000),((45036508956885875520879708969768515179661163640665163817157661:ℚ)/1186557521334900000000000000000000000000000000000000000000000000),((148118023:ℚ)/512000000)⟩
theorem valid24 : Valid source11 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((7558219701:ℚ)/10000000000),((1546992299:ℚ)/2000000000),((-10252946093:ℚ)/11630000000),((-91856856113:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1049042621:ℚ)/10000000000),((32546626547692486608454428408403969751931053448719134946557:ℚ)/858487808296729687500000000000000000000000000000000000000000),((148118023:ℚ)/512000000)⟩
theorem valid25 : Valid source11 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/8),((-13:ℚ)/16),((7677018431:ℚ)/10000000000),((7972540589:ℚ)/10000000000),((-52927784123:ℚ)/59100000000),((-93401239603:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((578222930560985676468599080240637658104549831153321341193249:ℚ)/14402019172331250000000000000000000000000000000000000000000000),((148118023:ℚ)/512000000)⟩
theorem valid26 : Valid source11 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((989326417:ℚ)/1250000000),((8447684857:ℚ)/10000000000),((-56253793999:ℚ)/61000000000),((-12061243421:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((103116583799173375598587553467634458044677021096382596567591:ℚ)/2326909907812500000000000000000000000000000000000000000000000),((148118023:ℚ)/512000000)⟩
theorem valid27 : Valid source11 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((8389780791:ℚ)/10000000000),((10348124827:ℚ)/10000000000),(-1:ℚ),((-102667150283:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1424698578237694736041241411890189043:ℚ)/24000000000000000000000000000000000000),((148118023:ℚ)/512000000)⟩
theorem valid28 : Valid source11 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((10290297567:ℚ)/10000000000),((353716031:ℚ)/250000000),(-1:ℚ),((-5537994277:ℚ)/9600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((752384000518420071962971:ℚ)/11520000000000000000000000),((148118023:ℚ)/512000000)⟩
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
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1743:ℚ)/2560) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((1743:ℚ)/2560) ((8753:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((8753:ℚ)/12800) ((8791:ℚ)/12800) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source11 nn0 nn1 Qcell ((8791:ℚ)/12800) ((8829:ℚ)/12800) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source11 nn0 nn1 Qcell ((8753:ℚ)/12800) ((8829:ℚ)/12800) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8829:ℚ)/12800) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((8829:ℚ)/12800) :=
  cell_join node0_7 node7_15
private theorem node16_18 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source11 nn0 nn1 Qcell ((8829:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_join leaf15 node16_18
private theorem node18_20 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_join leaf18 leaf19
private theorem node20_22 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf20 leaf21
private theorem node18_22 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join node18_20 node20_22
private theorem node15_22 :
    CellBound source11 nn0 nn1 Qcell ((8829:ℚ)/12800) ((45:ℚ)/64) :=
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
    CellBound source11 nn0 nn1 Qcell ((8829:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node15_22 node22_30
private theorem node0_30 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_30
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_30
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29]
theorem packet_count : packets.length = 30 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC03
#check @N11Formalization.C450Source11GroupedC03.bound
#print axioms N11Formalization.C450Source11GroupedC03.valid0
#print axioms N11Formalization.C450Source11GroupedC03.valid1
#print axioms N11Formalization.C450Source11GroupedC03.valid2
#print axioms N11Formalization.C450Source11GroupedC03.valid3
#print axioms N11Formalization.C450Source11GroupedC03.valid4
#print axioms N11Formalization.C450Source11GroupedC03.valid5
#print axioms N11Formalization.C450Source11GroupedC03.valid6
#print axioms N11Formalization.C450Source11GroupedC03.valid7
#print axioms N11Formalization.C450Source11GroupedC03.valid8
#print axioms N11Formalization.C450Source11GroupedC03.valid9
#print axioms N11Formalization.C450Source11GroupedC03.valid10
#print axioms N11Formalization.C450Source11GroupedC03.valid11
#print axioms N11Formalization.C450Source11GroupedC03.valid12
#print axioms N11Formalization.C450Source11GroupedC03.valid13
#print axioms N11Formalization.C450Source11GroupedC03.valid14
#print axioms N11Formalization.C450Source11GroupedC03.valid15
#print axioms N11Formalization.C450Source11GroupedC03.valid16
#print axioms N11Formalization.C450Source11GroupedC03.valid17
#print axioms N11Formalization.C450Source11GroupedC03.valid18
#print axioms N11Formalization.C450Source11GroupedC03.valid19
#print axioms N11Formalization.C450Source11GroupedC03.valid20
#print axioms N11Formalization.C450Source11GroupedC03.valid21
#print axioms N11Formalization.C450Source11GroupedC03.valid22
#print axioms N11Formalization.C450Source11GroupedC03.valid23
#print axioms N11Formalization.C450Source11GroupedC03.valid24
#print axioms N11Formalization.C450Source11GroupedC03.valid25
#print axioms N11Formalization.C450Source11GroupedC03.valid26
#print axioms N11Formalization.C450Source11GroupedC03.valid27
#print axioms N11Formalization.C450Source11GroupedC03.valid28
#print axioms N11Formalization.C450Source11GroupedC03.valid29
#print axioms N11Formalization.C450Source11GroupedC03.bound
#print axioms N11Formalization.C450Source11GroupedC03.endpoint_checks
