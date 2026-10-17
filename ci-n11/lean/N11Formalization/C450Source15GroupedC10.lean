import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6376231671:ℚ)/10000000000),((1665693659:ℚ)/2500000000),((-9579855613:ℚ)/24800000000),((-14648695013:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1150788423:ℚ)/2000000000),((1420876129537715292869162754722391248200623319054925184093:ℚ)/26464482031250000000000000000000000000000000000000000000000),((210947479246100389854993689:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3307213041:ℚ)/5000000000),((339094149:ℚ)/500000000),((-1957659043:ℚ)/5150000000),((-7681639123:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1287365491:ℚ)/2500000000),((151702096440505594038039793582646568541721240663317154011:ℚ)/2902710616381835937500000000000000000000000000000000000000),((51517951388342061239649449:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((3366752171:ℚ)/5000000000),((3450489259:ℚ)/5000000000),((-19993424813:ℚ)/52450000000),((-7860256513:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4821772483:ℚ)/10000000000),((542636366645864343652966192129761545514721929505188052669:ℚ)/10399394264062500000000000000000000000000000000000000000000),((50907639653903871370762689:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1713142719:ℚ)/2500000000),((3510030963:ℚ)/5000000000),((-20410216741:ℚ)/53400000000),((-4019428157:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((894434279:ℚ)/2000000000),((218105038732092546205502015108768284738359142336425667889:ℚ)/4186103385021972656250000000000000000000000000000000000000),((12574188799311657576258569:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6971626301:ℚ)/10000000000),((7079599279:ℚ)/10000000000),((-41237194953:ℚ)/108700000000),((-16434878903:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4095019159:ℚ)/10000000000),((533606373895679567716885214502562938513513566060921876093:ℚ)/10366251160083007812500000000000000000000000000000000000000),((198741180139279190179066129:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((703115003:ℚ)/1000000000),((7139133831:ℚ)/10000000000),((-41653936817:ℚ)/109650000000),((-1661345009:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((778724591:ℚ)/2000000000),((1863298697509461802864677417696718729594832471529427967:ℚ)/36217133082128906250000000000000000000000000000000000000),((1975173927266159999206561:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3545335597:ℚ)/5000000000),((899833207:ℚ)/1250000000),((-5258832449:ℚ)/13825000000),((-8396006791:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3681824713:ℚ)/10000000000),((240912319183301804389873485010050229644108004268131802873:ℚ)/4685046609667205810546875000000000000000000000000000000000),((49073256375696454620722161:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7150189859:ℚ)/10000000000),((7258194821:ℚ)/10000000000),((-42487363747:ℚ)/111550000000),((-16970569577:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3457709063:ℚ)/10000000000),((166079116809253172916408015982608031472972606459574591899:ℚ)/3231364488601684570312500000000000000000000000000000000000),((195068077190872860065383249:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((720970609:ℚ)/1000000000),((1463544279:ℚ)/2000000000),((-8580809953:ℚ)/22500000000),((-1714911827:ℚ)/5672500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((643739881:ℚ)/2000000000),((1318579080956811173466433540390958059775903865763037:ℚ)/25667646479736328125000000000000000000000000000000000),((1938425465317493665422249:ℚ)/18483200000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((7269219947:ℚ)/10000000000),((7377245441:ℚ)/10000000000),((-43320718087:ℚ)/113450000000),((-17327659841:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2961186461:ℚ)/10000000000),((136276391158921466541823432606208324941033123225639666003731:ℚ)/2654010273200000000000000000000000000000000000000000000000000),((192616432366558928942957761:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((732873149:ℚ)/1000000000),((7496286203:ℚ)/10000000000),((-4014000311:ℚ)/10400000000),((-1750619447:ℚ)/5815000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((669958991:ℚ)/2500000000),((828161405977508078953622479327710832798368539152231349:ℚ)/15976164617968750000000000000000000000000000000000000000),((5301654668528861344489:ℚ)/51200000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((372387393:ℚ)/500000000),((475957349:ℚ)/625000000),((-2811701443:ℚ)/7268750000),((-893162179:ℚ)/2955000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1002507457:ℚ)/5000000000),((89924498712503854529299572592433960703059236738341549:ℚ)/1736634531054687500000000000000000000000000000000000000),((472336443741689024861321:ℚ)/4620800000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((189168891:ℚ)/250000000),((1963338491:ℚ)/2500000000),((-59204921:ℚ)/150000000),((-455506673:ℚ)/1525000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((935676297:ℚ)/10000000000),((3503615744041922513699819581444326509873573500621829:ℚ)/66498339843750000000000000000000000000000000000000000),((116548168690677585053249:ℚ)/1155200000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((7804747037:ℚ)/10000000000),((8329332071:ℚ)/10000000000),((-49985324497:ℚ)/122000000000),((-18934241111:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((208699242713923912038744904647584855160360062502996536887:ℚ)/3842121600000000000000000000000000000000000000000000000000),((804147:ℚ)/8000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((4140321569:ℚ)/5000000000),((2046462641:ℚ)/2000000000),((-4220412829:ℚ)/8640000000),((-10180964707:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((676663619326695673149624356455379426611755033510054709399:ℚ)/10800000000000000000000000000000000000000000000000000000000),((804147:ℚ)/8000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((1018337449:ℚ)/1000000000),((7017904721:ℚ)/5000000000),((-44965333047:ℚ)/80000000000),((-2607012347:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((16777779734382206593947655341239280244923920010509213:ℚ)/233606400000000000000000000000000000000000000000000000),((804147:ℚ)/8000000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC10
#check @N11Formalization.C450Source15GroupedC10.bound
#print axioms N11Formalization.C450Source15GroupedC10.valid0
#print axioms N11Formalization.C450Source15GroupedC10.valid1
#print axioms N11Formalization.C450Source15GroupedC10.valid2
#print axioms N11Formalization.C450Source15GroupedC10.valid3
#print axioms N11Formalization.C450Source15GroupedC10.valid4
#print axioms N11Formalization.C450Source15GroupedC10.valid5
#print axioms N11Formalization.C450Source15GroupedC10.valid6
#print axioms N11Formalization.C450Source15GroupedC10.valid7
#print axioms N11Formalization.C450Source15GroupedC10.valid8
#print axioms N11Formalization.C450Source15GroupedC10.valid9
#print axioms N11Formalization.C450Source15GroupedC10.valid10
#print axioms N11Formalization.C450Source15GroupedC10.valid11
#print axioms N11Formalization.C450Source15GroupedC10.valid12
#print axioms N11Formalization.C450Source15GroupedC10.valid13
#print axioms N11Formalization.C450Source15GroupedC10.valid14
#print axioms N11Formalization.C450Source15GroupedC10.valid15
#print axioms N11Formalization.C450Source15GroupedC10.bound
#print axioms N11Formalization.C450Source15GroupedC10.endpoint_checks
