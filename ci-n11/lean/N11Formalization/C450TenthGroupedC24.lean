import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((3006078163:ℚ)/5000000000),((6528794871:ℚ)/10000000000),((23602547141:ℚ)/53400000000),((7248794871:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((16455873:ℚ)/25000000),((1709644594063497348041663:ℚ)/712890000000000000000000000),((-509415007530094756175390557:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6487715123:ℚ)/10000000000),((211453383:ℚ)/312500000),((50534005861:ℚ)/110600000000),((77984461:ℚ)/139062500),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2739246177:ℚ)/5000000000),((64115261434702582424415847302911683:ℚ)/91742700000000000000000000000000000000),((-2065409133630711145746286237:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((6725465677:ℚ)/10000000000),((1377071907:ℚ)/2000000000),((17399419913:ℚ)/37500000000),((1521071907:ℚ)/2765000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2422266487:ℚ)/5000000000),((-181568519475009445264528133740277:ℚ)/3515625000000000000000000000000000000),((-2079392855106120660228455837:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6844334597:ℚ)/10000000000),((3502103723:ℚ)/5000000000),((53030342179:ℚ)/114400000000),((3862103723:ℚ)/7031250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2248582929:ℚ)/5000000000),((-4559168375525841855954068223158533:ℚ)/32718400000000000000000000000000000000),((-2086412050931410961645600077:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((6963199561:ℚ)/10000000000),((7063630191:ℚ)/10000000000),((17954132309:ℚ)/38450000000),((7783630191:ℚ)/14300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((412277859:ℚ)/1000000000),((-2657938667078833221335613419488123:ℚ)/5544009375000000000000000000000000000),((-2093449484231892584263859813:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((351131531:ℚ)/500000000),((3561526077:ℚ)/5000000000),((2713920717:ℚ)/5815000000),((1307175359:ℚ)/2403125000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3923048029:ℚ)/10000000000),((-8684507152561010932201450107061:ℚ)/16907112500000000000000000000000000),((-5242437607375837256319533:ℚ)/36966400000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/16),((1:ℚ)/2),((7082060763:ℚ)/10000000000),((1795618339:ℚ)/2500000000),((54694425341:ℚ)/117250000000),((1975618339:ℚ)/3634375000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3713175219:ℚ)/10000000000),((-28151199395289350603811865887534499:ℚ)/51553359375000000000000000000000000000),((-2100505164694405204201193357:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7141490011:ℚ)/10000000000),((3620946907:ℚ)/5000000000),((18370143359:ℚ)/39400000000),((568706701:ℚ)/1046875000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((872831871:ℚ)/2500000000),((-1119003251566367588389467672104533:ℚ)/1940450000000000000000000000000000000),((-2104039850500439231764432013:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((1440183677:ℚ)/2000000000),((7301313547:ℚ)/10000000000),((11105285739:ℚ)/23830000000),((8021313547:ℚ)/14775000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((130202117:ℚ)/400000000),((-2579022959481374741338181394913097:ℚ)/4259016750000000000000000000000000000),((-84303164056452082592771837:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((1815086477:ℚ)/2500000000),((7360732571:ℚ)/10000000000),((13985605339:ℚ)/30025000000),((8080732571:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3000941149:ℚ)/10000000000),((-356498880775246206331111259581339:ℚ)/563437890625000000000000000000000000),((-131945182412233171849745437:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((3659886299:ℚ)/5000000000),((7420150903:ℚ)/10000000000),((3131022677:ℚ)/6725000000),((8140150903:ℚ)/15012500000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1361999861:ℚ)/5000000000),((-74423853808761107244691757893791:ℚ)/113064062500000000000000000000000000),((-528667825732716768832915853:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((1844799619:ℚ)/2500000000),((93494607:ℚ)/125000000),((14193597333:ℚ)/30500000000),((34164869:ℚ)/63046875),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((302048269:ℚ)/1250000000),((-26007289427415847208154030320671:ℚ)/38125000000000000000000000000000000),((-132389015967433101832123133:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7438623561:ℚ)/10000000000),((7717232737:ℚ)/10000000000),((57190364927:ℚ)/125800000000),((8437232737:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((516107011:ℚ)/2500000000),((127777138387874155488165233297801:ℚ)/19782050000000000000000000000000000000),((-2121781777188856406432243813:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((3838158163:ℚ)/5000000000),((3977443639:ℚ)/5000000000),((29427107141:ℚ)/64800000000),((4337443639:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-969197987443044671559010174962467:ℚ)/10497600000000000000000000000000000000),((-147608447:ℚ)/1024000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((3956998887:ℚ)/5000000000),((1971171829:ℚ)/2000000000),((30258992209:ℚ)/80000000000),((2115171829:ℚ)/3240000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((55921497125815349301025330700015119:ℚ)/12000000000000000000000000000000000000),((-147608447:ℚ)/1024000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((19170193:ℚ)/19531250),((3414249919:ℚ)/2500000000),((144191351:ℚ)/431250000),((3594249919:ℚ)/5000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((431821042055036602523:ℚ)/46494140625000000000000),((-147608447:ℚ)/1024000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC24
#check @N11Formalization.C450TenthGroupedC24.bound
#print axioms N11Formalization.C450TenthGroupedC24.valid0
#print axioms N11Formalization.C450TenthGroupedC24.valid1
#print axioms N11Formalization.C450TenthGroupedC24.valid2
#print axioms N11Formalization.C450TenthGroupedC24.valid3
#print axioms N11Formalization.C450TenthGroupedC24.valid4
#print axioms N11Formalization.C450TenthGroupedC24.valid5
#print axioms N11Formalization.C450TenthGroupedC24.valid6
#print axioms N11Formalization.C450TenthGroupedC24.valid7
#print axioms N11Formalization.C450TenthGroupedC24.valid8
#print axioms N11Formalization.C450TenthGroupedC24.valid9
#print axioms N11Formalization.C450TenthGroupedC24.valid10
#print axioms N11Formalization.C450TenthGroupedC24.valid11
#print axioms N11Formalization.C450TenthGroupedC24.valid12
#print axioms N11Formalization.C450TenthGroupedC24.valid13
#print axioms N11Formalization.C450TenthGroupedC24.valid14
#print axioms N11Formalization.C450TenthGroupedC24.valid15
#print axioms N11Formalization.C450TenthGroupedC24.bound
#print axioms N11Formalization.C450TenthGroupedC24.endpoint_checks
