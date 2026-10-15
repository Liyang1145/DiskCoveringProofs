import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((6980605539:ℚ)/10000000000),((3569687501:ℚ)/5000000000),(-1:ℚ),((-18125816617:ℚ)/20030000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((4065242953:ℚ)/10000000000),((545015753949321347801497765544711:ℚ)/2507505625000000000000000000000000),((436466779944976425210279:ℚ)/451250000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((704004601:ℚ)/1000000000),((3599375001:ℚ)/5000000000),(-1:ℚ),((-1830413803:ℚ)/2022000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((3862670323:ℚ)/10000000000),((15410159134866450345263385702659:ℚ)/70980625000000000000000000000000),((1314324435657053191255837:ℚ)/1353750000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7099485249:ℚ)/10000000000),((3614218751:ℚ)/5000000000),(-1:ℚ),((-18482455747:ℚ)/20315000000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((3649466703:ℚ)/10000000000),((6915365850040869143919511340730607:ℚ)/32242126953125000000000000000000000),((438930113962605765835279:ℚ)/451250000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7129204417:ℚ)/10000000000),((3629062501:ℚ)/5000000000),(-1:ℚ),((-18571613251:ℚ)/20410000000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((3538280231:ℚ)/10000000000),((4128331411755206813958869708291:ℚ)/19257031250000000000000000000000),((439752940110572056460279:ℚ)/451250000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((8183:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7158923289:ℚ)/10000000000),((454560547:ℚ)/625000000),(-1:ℚ),((-18660769867:ℚ)/20457500000),((9888211123:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((37416203:ℚ)/250000000),((3423642321:ℚ)/10000000000),((1137507479651799732319475140510069:ℚ)/5338128906250000000000000000000000),((6877573042362453866811:ℚ)/7050781250000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8183:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((8183:ℚ)/12800),((4101:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((896722827:ℚ)/1250000000),((3643906251:ℚ)/5000000000),(-1:ℚ),((-2338168481:ℚ)/2563125000),((4940065779:ℚ)/5000000000),((1236026391:ℚ)/1250000000),((774947369:ℚ)/5000000000),((210307443:ℚ)/625000000),((24299073668342231571044229312559:ℚ)/114055725097656250000000000000000),((1321729870988749806880837:ℚ)/1353750000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((8183:ℚ)/12800) ((4101:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4101:ℚ)/6400),((8221:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7188641871:ℚ)/10000000000),((1825664063:ℚ)/2500000000),(-1:ℚ),((-18749925613:ℚ)/20552500000),((4936061823:ℚ)/5000000000),((9880131563:ℚ)/10000000000),((320187229:ℚ)/2000000000),((103287291:ℚ)/312500000),((56232859455680892542410590207817577:ℚ)/264003285156250000000000000000000000),((110247196741432680228351:ℚ)/112812500000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8221:ℚ)/12800),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((3601750527:ℚ)/5000000000),((3658750001:ℚ)/5000000000),(-1:ℚ),((-9397251581:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((9872123651:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((81110239:ℚ)/250000000),((3530077965341003087990348883264887:ℚ)/16576562500000000000000000000000000),((441401164619639403335279:ℚ)/451250000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((8221:ℚ)/12800) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1443672033:ℚ)/2000000000),((916542969:ℚ)/1250000000),(-1:ℚ),((-3767816099:ℚ)/4129500000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((1591253573:ℚ)/5000000000),((63033588300035853862265694124493:ℚ)/296055039062500000000000000000000),((82840079367120496792357:ℚ)/84609375000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3616609603:ℚ)/5000000000),((3673593751:ℚ)/5000000000),(-1:ℚ),((-9441828809:ℚ)/10347500000),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((779854849:ℚ)/2500000000),((712247565663494297788125210710791:ℚ)/3345961132812500000000000000000000),((442226562980740459585279:ℚ)/451250000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7248078177:ℚ)/10000000000),((1840507813:ℚ)/2500000000),(-1:ℚ),((-18928234531:ℚ)/20742500000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((381884101:ℚ)/1250000000),((57229974562896118178521928986882181:ℚ)/268907066406250000000000000000000000),((110659895921983208353351:ℚ)/112812500000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7262937077:ℚ)/10000000000),((3688437501:ℚ)/5000000000),(-1:ℚ),((-1724801021:ℚ)/1890000000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((1494693013:ℚ)/5000000000),((34909422021957227765174074097:ℚ)/164062500000000000000000000000),((1329158456238659313130837:ℚ)/1353750000000000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((7277795909:ℚ)/10000000000),((230991211:ℚ)/312500000),(-1:ℚ),((-19017387727:ℚ)/20837500000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((2922268591:ℚ)/10000000000),((57732092861253362419716013283994953:ℚ)/271375878906250000000000000000000000),((1732290109982817470609:ℚ)/1762695312500000000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7292654671:ℚ)/10000000000),((3703281251:ℚ)/5000000000),(-1:ℚ),((-19061964013:ℚ)/20885000000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((2853619493:ℚ)/10000000000),((14496010343232125970222927693455711:ℚ)/68153628906250000000000000000000000),((443879931916077337710279:ℚ)/451250000000000000000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1461502673:ℚ)/2000000000),((3718125001:ℚ)/5000000000),(-1:ℚ),((-3821308019:ℚ)/4196000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1391662657:ℚ)/5000000000),((294088649416503532437201523476379:ℚ)/1375501250000000000000000000000000),((444707902490313159585279:ℚ)/451250000000000000000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((146744611:ℚ)/200000000),((3732968751:ℚ)/5000000000),(-1:ℚ),((-383913833:ℚ)/421500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((2637272187:ℚ)/10000000000),((527346616022123679057655810741:ℚ)/2467531250000000000000000000000),((1336610191406781710005837:ℚ)/1353750000000000000000000)⟩
theorem valid15 : Valid source23 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source23 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7366947467:ℚ)/10000000000),((3747812501:ℚ)/5000000000),(-1:ℚ),((-19284842401:ℚ)/21170000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((155178383:ℚ)/625000000),((14959407430482567105187768457922733:ℚ)/70026390625000000000000000000000000),((446366415851919568960279:ℚ)/451250000000000000000000)⟩
theorem valid16 : Valid source23 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source23 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((7396664119:ℚ)/10000000000),((3777500001:ℚ)/5000000000),(-1:ℚ),((-19373992357:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((579599887:ℚ)/2500000000),((854547225381322661893310398911017:ℚ)/3960500000000000000000000000000000),((1344085076493116997505837:ℚ)/1353750000000000000000000)⟩
theorem valid17 : Valid source23 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1491219329:ℚ)/2000000000),((3836875001:ℚ)/5000000000),(-1:ℚ),((-3910457987:ℚ)/4348000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((243635929:ℚ)/1250000000),((649473633239681228626239479525707:ℚ)/2953922500000000000000000000000000),((995657:ℚ)/1000000)⟩
theorem valid18 : Valid source23 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((1893739669:ℚ)/2500000000),((3896250001:ℚ)/5000000000),(-1:ℚ),((-4977219007:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((162400051:ℚ)/2000000000),((18719437890572885071052285835377:ℚ)/85326171875000000000000000000000),((995657:ℚ)/1000000)⟩
theorem valid19 : Valid source23 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((1923454213:ℚ)/2500000000),((4015000001:ℚ)/5000000000),(-1:ℚ),((-389720203:ℚ)/440000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((6859805288377267655047831651073:ℚ)/30250000000000000000000000000000),((995657:ℚ)/1000000)⟩
theorem valid20 : Valid source23 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((7931522411:ℚ)/10000000000),((4490000001:ℚ)/5000000000),(-1:ℚ),((-20978567233:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1022480056557731898078504306648161:ℚ)/3888000000000000000000000000000000),((995657:ℚ)/1000000)⟩
theorem valid21 : Valid source23 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((4441111987:ℚ)/5000000000),((5440000001:ℚ)/5000000000),(-1:ℚ),((-11915335961:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((11522316569163297314874143892853897:ℚ)/40000000000000000000000000000000000),((995657:ℚ)/1000000)⟩
theorem valid22 : Valid source23 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((10783226897:ℚ)/10000000000),((14680000003:ℚ)/10000000000),(-1:ℚ),((-29533680691:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1102174179554921257597133:ℚ)/3385600000000000000000000),((995657:ℚ)/1000000)⟩
theorem valid23 : Valid source23 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet23 valid23
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((2003:ℚ)/3200) ((4063:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((4063:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((4063:ℚ)/6400) ((4101:ℚ)/6400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((4101:ℚ)/6400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((8221:ℚ)/12800) ((8259:ℚ)/12800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8259:ℚ)/12800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source23 nn0 nn1 Qcell ((8259:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source23 nn0 nn1 Qcell ((4101:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source23 nn0 nn1 Qcell ((1667:ℚ)/2560) ((1049:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source23 nn0 nn1 Qcell ((843:ℚ)/1280) ((267:ℚ)/400) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf18 node19_21
private theorem node22_24 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf21 node22_24
private theorem node18_24 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node18_21 node21_24
private theorem node12_24 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node12_18 node18_24
private theorem node0_24 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_24
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_24
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23]
theorem packet_count : packets.length = 24 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC01
#check @N11Formalization.C450Source23GroupedC01.bound
#print axioms N11Formalization.C450Source23GroupedC01.valid0
#print axioms N11Formalization.C450Source23GroupedC01.valid1
#print axioms N11Formalization.C450Source23GroupedC01.valid2
#print axioms N11Formalization.C450Source23GroupedC01.valid3
#print axioms N11Formalization.C450Source23GroupedC01.valid4
#print axioms N11Formalization.C450Source23GroupedC01.valid5
#print axioms N11Formalization.C450Source23GroupedC01.valid6
#print axioms N11Formalization.C450Source23GroupedC01.valid7
#print axioms N11Formalization.C450Source23GroupedC01.valid8
#print axioms N11Formalization.C450Source23GroupedC01.valid9
#print axioms N11Formalization.C450Source23GroupedC01.valid10
#print axioms N11Formalization.C450Source23GroupedC01.valid11
#print axioms N11Formalization.C450Source23GroupedC01.valid12
#print axioms N11Formalization.C450Source23GroupedC01.valid13
#print axioms N11Formalization.C450Source23GroupedC01.valid14
#print axioms N11Formalization.C450Source23GroupedC01.valid15
#print axioms N11Formalization.C450Source23GroupedC01.valid16
#print axioms N11Formalization.C450Source23GroupedC01.valid17
#print axioms N11Formalization.C450Source23GroupedC01.valid18
#print axioms N11Formalization.C450Source23GroupedC01.valid19
#print axioms N11Formalization.C450Source23GroupedC01.valid20
#print axioms N11Formalization.C450Source23GroupedC01.valid21
#print axioms N11Formalization.C450Source23GroupedC01.valid22
#print axioms N11Formalization.C450Source23GroupedC01.valid23
#print axioms N11Formalization.C450Source23GroupedC01.bound
#print axioms N11Formalization.C450Source23GroupedC01.endpoint_checks
