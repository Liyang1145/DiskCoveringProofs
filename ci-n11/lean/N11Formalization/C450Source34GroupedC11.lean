import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((12655479:ℚ)/19531250),((1673532779:ℚ)/2500000000),((-2460598337:ℚ)/12400000000),((-2936986:ℚ)/26328125),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5498945441:ℚ)/10000000000),((303554365897696957966177427895006933:ℚ)/2383280000000000000000000000000000000),((208026077768475788837:ℚ)/4230468750000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6600661379:ℚ)/10000000000),((212972783:ℚ)/312500000),((-318918349:ℚ)/1579687500),((-2376661379:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((5186118731:ℚ)/10000000000),((198722402397412063780313738167348693158786733888537:ℚ)/1539832846820354461669921875000000000000000000000000),((123335739524339599141255257:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6721630029:ℚ)/10000000000),((6875596351:ℚ)/10000000000),((-10386789053:ℚ)/51500000000),((-832543343:ℚ)/6930000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2427679257:ℚ)/5000000000),((427110810604160994054577739423351342442661739929903829:ℚ)/3334738159179687500000000000000000000000000000000000000),((303165831203013282059780971:ℚ)/8871936000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6782083103:ℚ)/10000000000),((6936043323:ℚ)/10000000000),((-10568129969:ℚ)/51975000000),((-2558083103:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4682059457:ℚ)/10000000000),((489678075767672587986074945386089976050447633618561287:ℚ)/3798844628906250000000000000000000000000000000000000000),((89841612501820038170318993:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((3421258063:ℚ)/5000000000),((6996470539:ℚ)/10000000000),((-10749411617:ℚ)/52450000000),((-1309258063:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2251333453:ℚ)/5000000000),((116973605961972411000332613775787388124642107327128733241:ℚ)/901813007031250000000000000000000000000000000000000000000),((19644729717087468328721713:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((862866207:ℚ)/1250000000),((1411375709:ℚ)/2000000000),((-2186127127:ℚ)/10585000000),((-111622069:ℚ)/890000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2158207669:ℚ)/5000000000),((725492610680655049539201333008356189178368239740627957:ℚ)/5559220085742187500000000000000000000000000000000000000),((3153147372174359166698419:ℚ)/138624000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((6963324231:ℚ)/10000000000),((1423453573:ℚ)/2000000000),((-2222360719:ℚ)/10680000000),((-2739324231:ℚ)/21550000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2061184593:ℚ)/5000000000),((2998614866276048477540831648418321161541314703369698621:ℚ)/22840995600000000000000000000000000000000000000000000000),((464594769767271579249931:ℚ)/24576000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((7023700371:ℚ)/10000000000),((7177639007:ℚ)/10000000000),((-11292917021:ℚ)/53875000000),((-2799700371:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((783872947:ℚ)/2000000000),((129055329259535659056347449902950702705816139635427012877:ℚ)/977331433105468750000000000000000000000000000000000000000),((133488450094235570476201771:ℚ)/8871936000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((283362343:ℚ)/400000000),((7237992459:ℚ)/10000000000),((-11473977377:ℚ)/54350000000),((-114402343:ℚ)/877200000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((115810117:ℚ)/312500000),((24985451645225333684100600379092215633536004840988980923:ℚ)/188139477978515625000000000000000000000000000000000000000),((52858936658900960795073:ℚ)/4731699200000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7144399323:ℚ)/10000000000),((7298328691:ℚ)/10000000000),((-11654986073:ℚ)/54825000000),((-2920399323:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((21750749:ℚ)/62500000),((3198714170988408651588308389361199517179831641643293027:ℚ)/23952314355468750000000000000000000000000000000000000000),((178905112840847971685059:ℚ)/24576000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((3602361541:ℚ)/5000000000),((7418951299:ℚ)/10000000000),((-12016853897:ℚ)/55300000000),((-1490361541:ℚ)/11250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3239361739:ℚ)/10000000000),((2946953421458760800897669457618132919890828367296207649:ℚ)/21570456250000000000000000000000000000000000000000000000),((2492586370868144879375337:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((3662660701:ℚ)/5000000000),((1884877569:ℚ)/2500000000),((-3094632707:ℚ)/14062500000),((-1550660701:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2696729507:ℚ)/10000000000),((2398452006304824527714100522809415261664903141084816211:ℚ)/17380714416503906250000000000000000000000000000000000000),((-3323393674776703811349223:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((930732117:ℚ)/1250000000),((125330797:ℚ)/156250000),((-215992391:ℚ)/893750000),((-402732117:ℚ)/3050000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((252183683:ℚ)/1250000000),((510786715192488685006477925566448342978283819807109:ℚ)/3346489334106445312500000000000000000000000000000000),((-1722902075868271661245541:ℚ)/138624000000000000000000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((3963715749:ℚ)/5000000000),((8502035971:ℚ)/10000000000),((-15266107913:ℚ)/61000000000),((-617238583:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((55536350066155714301236907884150202208919719523846404361:ℚ)/354657812500000000000000000000000000000000000000000000000),((-4644333:ℚ)/204800000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((4204110387:ℚ)/5000000000),((2604962217:ℚ)/2500000000),((-5254886651:ℚ)/16200000000),((-2092110387:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1016905432636580717877803767650568733313960721633215361:ℚ)/4982259375000000000000000000000000000000000000000000000),((-4644333:ℚ)/204800000)⟩
theorem valid14 : Valid source34 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10325804751:ℚ)/10000000000),((712032011:ℚ)/500000000),((-1624096033:ℚ)/4000000000),((-2033934917:ℚ)/14720000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4309382656548666671469856860760731:ℚ)/16000000000000000000000000000000000),((-4644333:ℚ)/204800000)⟩
theorem valid15 : Valid source34 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC11
#check @N11Formalization.C450Source34GroupedC11.bound
#print axioms N11Formalization.C450Source34GroupedC11.valid0
#print axioms N11Formalization.C450Source34GroupedC11.valid1
#print axioms N11Formalization.C450Source34GroupedC11.valid2
#print axioms N11Formalization.C450Source34GroupedC11.valid3
#print axioms N11Formalization.C450Source34GroupedC11.valid4
#print axioms N11Formalization.C450Source34GroupedC11.valid5
#print axioms N11Formalization.C450Source34GroupedC11.valid6
#print axioms N11Formalization.C450Source34GroupedC11.valid7
#print axioms N11Formalization.C450Source34GroupedC11.valid8
#print axioms N11Formalization.C450Source34GroupedC11.valid9
#print axioms N11Formalization.C450Source34GroupedC11.valid10
#print axioms N11Formalization.C450Source34GroupedC11.valid11
#print axioms N11Formalization.C450Source34GroupedC11.valid12
#print axioms N11Formalization.C450Source34GroupedC11.valid13
#print axioms N11Formalization.C450Source34GroupedC11.valid14
#print axioms N11Formalization.C450Source34GroupedC11.valid15
#print axioms N11Formalization.C450Source34GroupedC11.bound
#print axioms N11Formalization.C450Source34GroupedC11.endpoint_checks
