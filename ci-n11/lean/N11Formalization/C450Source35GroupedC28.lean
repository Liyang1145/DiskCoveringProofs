import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((11:ℚ)/16),((3:ℚ)/4),((5114394833:ℚ)/10000000000),((682279183:ℚ)/1250000000),((77378343163:ℚ)/103000000000),((2726837549:ℚ)/3100000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8326110469:ℚ)/10000000000),((-269274406453364742622189749222216769:ℚ)/767118250000000000000000000000000000),((-7393829618317452208422251:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5354339669:ℚ)/10000000000),((5698314203:ℚ)/10000000000),((80017736359:ℚ)/106800000000),((22534942609:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7890520519:ℚ)/10000000000),((-39369398654908632882217378422339394413993026488076851507:ℚ)/111296886062622070312500000000000000000000000000000000000),((-466292753079254457619299731:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((223764321:ℚ)/400000000),((5818285853:ℚ)/10000000000),((3306207531:ℚ)/4348000000),((22894857559:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7435549389:ℚ)/10000000000),((-1778891038442178213997424775009152385028887245347930185651:ℚ)/4789383143750000000000000000000000000000000000000000000000),((-462745414910172432516271331:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((2856965957:ℚ)/5000000000),((5938214903:ℚ)/10000000000),((5998089361:ℚ)/7900000000),((23254644709:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((7199584189:ℚ)/10000000000),((-57589251266073131876927953670207239364932843593842331571:ℚ)/154823112086486816406250000000000000000000000000000000000),((-459137296120863312421097531:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((5833718423:ℚ)/10000000000),((2999082073:ℚ)/5000000000),((85290902653:ℚ)/111550000000),((1673892317:ℚ)/1975000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3478583587:ℚ)/5000000000),((-2549518173028927578561277744775997593763793310949710123:ℚ)/6713684136962890625000000000000000000000000000000000000),((-114327610860812997696406811:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((2946799133:ℚ)/5000000000),((23664467:ℚ)/39062500),((42974790463:ℚ)/56250000000),((737947208:ℚ)/871484375),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3416658511:ℚ)/5000000000),((-55247542465794925870748539380196045232175079206377:ℚ)/145432468735089059919118881225585937500000000000000),((-6949896163146633919151:ℚ)/14101562500000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((1488367369:ℚ)/2500000000),((6118033373:ℚ)/10000000000),((21652041059:ℚ)/28362500000),((23794100119:ℚ)/28125000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3353785871:ℚ)/5000000000),((-33303278638360782986718119625732169695138815236313119379:ℚ)/87637424468994140625000000000000000000000000000000000000),((-453611150421495290290695011:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6013332273:ℚ)/10000000000),((1544488463:ℚ)/2500000000),((7933332273:ℚ)/10400000000),((5993465389:ℚ)/7090625000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6579819369:ℚ)/10000000000),((-11010628807258984724956786059477626213174227965471965553:ℚ)/28965226062202453613281250000000000000000000000000000000),((-28233669354432816317528171:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6073186869:ℚ)/10000000000),((6237865223:ℚ)/10000000000),((29308351853:ℚ)/38450000000),((24153595669:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((161248433:ℚ)/250000000),((-1670052359573264821981944981825930112274789009685579781:ℚ)/4392021841796875000000000000000000000000000000000000000),((-449851072535783610865928411:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((11978581:ℚ)/19531250),((1259553543:ℚ)/2000000000),((346028782:ℚ)/454296875),((4866660629:ℚ)/5767500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1263558181:ℚ)/2000000000),((-58934437000213031354179891835860662584116362785631825383:ℚ)/154945879765722656250000000000000000000000000000000000000),((-17917929550885061063734491:ℚ)/36966400000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((154821807:ℚ)/250000000),((6357661547:ℚ)/10000000000),((2231039877:ℚ)/2931250000),((24512984641:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1545807897:ℚ)/2500000000),((-27410582345407289897179230814595935985009921914002848227029:ℚ)/72046357748339843750000000000000000000000000000000000000000),((-446030208219861758971671731:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1250540697:ℚ)/2000000000),((6417546931:ℚ)/10000000000),((5993315889:ℚ)/7880000000),((24692640793:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1511523723:ℚ)/2500000000),((-2950273479920509047060646357206708821084789273196149634501:ℚ)/7752554578018188476562500000000000000000000000000000000000),((-444096980718515738207386499:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6312527273:ℚ)/10000000000),((809678009:ℚ)/1250000000),((90557800003:ℚ)/119150000000),((3109034027:ℚ)/3693750000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5906197879:ℚ)/10000000000),((-95237608921642130942931593922996029196475621405848858023:ℚ)/250198844499206542968750000000000000000000000000000000000),((-6908571189318003453772379:ℚ)/14440000000000000000000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((254893753:ℚ)/400000000),((653729317:ℚ)/1000000000),((3648631283:ℚ)/4804000000),((2505187951:ℚ)/2978750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((720417013:ℚ)/1250000000),((-18883786056795011346145723180873517034404157007485821839:ℚ)/49598118225973510742187500000000000000000000000000000000),((-4401849342136300627023251:ℚ)/9241600000000000000000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((1286430663:ℚ)/2000000000),((416063:ℚ)/625000),((18374737293:ℚ)/24400000000),((3176378:ℚ)/3753125),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1123455979:ℚ)/2000000000),((-15091676310804103941695889924801047969646373221:ℚ)/40310569633865356445312500000000000000000000000),((-1703953507453126571:ℚ)/3610000000000000000)⟩
theorem valid14 : Valid source35 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((204742243:ℚ)/312500000),((6776692889:ℚ)/10000000000),((2912164673:ℚ)/3871875000),((25770078667:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((166078457:ℚ)/312500000),((-82322736382699552875044814415210920993801626064337378678517:ℚ)/219710514843750000000000000000000000000000000000000000000000),((-432178470596789341712208539:ℚ)/924160000000000000000000000)⟩
theorem valid15 : Valid source35 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1334264789:ℚ)/2000000000),((6896349213:ℚ)/10000000000),((18900912679:ℚ)/25160000000),((26129047639:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((249767101:ℚ)/500000000),((-61876754911120792976052598022422041566484871135786502683:ℚ)/165018011791992187500000000000000000000000000000000000000),((-428084051204072901850131171:ℚ)/924160000000000000000000000)⟩
theorem valid16 : Valid source35 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source35 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((1697717757:ℚ)/2500000000),((1783895317:ℚ)/2500000000),((7984965109:ℚ)/10800000000),((6711685951:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2328185863:ℚ)/5000000000),((-805120346354529377310783274513515662322431887863798649:ℚ)/2216787341308593750000000000000000000000000000000000000),((-26232051993145700310819251:ℚ)/57760000000000000000000000)⟩
theorem valid17 : Valid source35 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((7029894407:ℚ)/10000000000),((8091591971:ℚ)/10000000000),((98448838477:ℚ)/144800000000),((29714775913:ℚ)/32400000000),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((3897972973:ℚ)/10000000000),((-234940789388019892754590232479727137426269583752440258911:ℚ)/801590175000000000000000000000000000000000000000000000000),((-27891773:ℚ)/64000000)⟩
theorem valid18 : Valid source35 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7985181839:ℚ)/10000000000),((9046451793:ℚ)/10000000000),((108957000229:ℚ)/160000000000),((32579355379:ℚ)/36200000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-22657757378073644291259574347211488765690281835118994051:ℚ)/74121762500000000000000000000000000000000000000000000000),((-27891773:ℚ)/64000000)⟩
theorem valid19 : Valid source35 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source35 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((4469728907:ℚ)/5000000000),((12859168309:ℚ)/10000000000),((59727017977:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-9625679626801:ℚ)/69000000000000),((-27891773:ℚ)/64000000)⟩
theorem valid20 : Valid source35 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source35 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source35 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source35 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source35 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source35 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC28
#check @N11Formalization.C450Source35GroupedC28.bound
#print axioms N11Formalization.C450Source35GroupedC28.valid0
#print axioms N11Formalization.C450Source35GroupedC28.valid1
#print axioms N11Formalization.C450Source35GroupedC28.valid2
#print axioms N11Formalization.C450Source35GroupedC28.valid3
#print axioms N11Formalization.C450Source35GroupedC28.valid4
#print axioms N11Formalization.C450Source35GroupedC28.valid5
#print axioms N11Formalization.C450Source35GroupedC28.valid6
#print axioms N11Formalization.C450Source35GroupedC28.valid7
#print axioms N11Formalization.C450Source35GroupedC28.valid8
#print axioms N11Formalization.C450Source35GroupedC28.valid9
#print axioms N11Formalization.C450Source35GroupedC28.valid10
#print axioms N11Formalization.C450Source35GroupedC28.valid11
#print axioms N11Formalization.C450Source35GroupedC28.valid12
#print axioms N11Formalization.C450Source35GroupedC28.valid13
#print axioms N11Formalization.C450Source35GroupedC28.valid14
#print axioms N11Formalization.C450Source35GroupedC28.valid15
#print axioms N11Formalization.C450Source35GroupedC28.valid16
#print axioms N11Formalization.C450Source35GroupedC28.valid17
#print axioms N11Formalization.C450Source35GroupedC28.valid18
#print axioms N11Formalization.C450Source35GroupedC28.valid19
#print axioms N11Formalization.C450Source35GroupedC28.valid20
#print axioms N11Formalization.C450Source35GroupedC28.bound
#print axioms N11Formalization.C450Source35GroupedC28.endpoint_checks
