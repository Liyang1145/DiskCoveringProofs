import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/2),((9:ℚ)/16),((22001827:ℚ)/40000000),((1165838393:ℚ)/2000000000),((30641827:ℚ)/51500000),((14076545537:ℚ)/19840000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((951979169:ℚ)/1250000000),((-396431320242596076082294779975158570222990683198100253445271:ℚ)/1553462324428800000000000000000000000000000000000000000000000),((-236042603588480474652991:ℚ)/577600000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((1148109983:ℚ)/2000000000),((6069147073:ℚ)/10000000000),((1580109983:ℚ)/2670000000),((72542323657:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7146303861:ℚ)/10000000000),((-30846822687263075717409605155820504631685839557594113476138317:ℚ)/121717836098437500000000000000000000000000000000000000000000000),((-5854344004474575496120911:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((5980455731:ℚ)/10000000000),((788616379:ℚ)/1250000000),((8140455731:ℚ)/13825000000),((9337547411:ℚ)/13350000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6650238473:ℚ)/10000000000),((-53673120854476212120034943345840482686031966593425307139613:ℚ)/213164734602062988281250000000000000000000000000000000000000),((-181356938952320749582263:ℚ)/451250000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((3110096941:ℚ)/5000000000),((100449443:ℚ)/156250000),((4190096941:ℚ)/7031250000),((1184044987:ℚ)/1728125000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6120941287:ℚ)/10000000000),((-327519994878942669792572077400428643927209364088971:ℚ)/1275735212210565805435180664062500000000000000000000),((-90710556822859082208599:ℚ)/225625000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((634000549:ℚ)/1000000000),((6548561211:ℚ)/10000000000),((850000549:ℚ)/1430000000),((76857050899:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1168190857:ℚ)/2000000000),((-46558563865576564053942540625897712832475312019591075196090271:ℚ)/181974133300781250000000000000000000000000000000000000000000000),((-17332151121637464054643717:ℚ)/43320000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((25233521:ℚ)/39062500),((266732937:ℚ)/400000000),((269368168:ℚ)/454296875),((3117396433:ℚ)/4576000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((21674439:ℚ)/39062500),((-18778436876835537991738446869541837924385949901498429071407:ℚ)/73638478899814400000000000000000000000000000000000000000000),((-27591573990291452202013:ℚ)/69312000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3289761661:ℚ)/5000000000),((3394026347:ℚ)/5000000000),((4369761661:ℚ)/7387500000),((39506237123:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((524195769:ℚ)/1000000000),((-9092688553884194068668178940262394592066210668243147377276109:ℚ)/35770325345697070312500000000000000000000000000000000000000000),((-1429514689556872867718631:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((6699232989:ℚ)/10000000000),((6907750607:ℚ)/10000000000),((8859232989:ℚ)/15012500000),((80089755463:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2459066477:ℚ)/5000000000),((-2829515831057416950088942519233306453415249816462454649434659921:ℚ)/11165539831330162500000000000000000000000000000000000000000000000),((-5686826704131120922866991:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((106545499:ℚ)/156250000),((7027418651:ℚ)/10000000000),((140295499:ℚ)/238281250),((81166767859:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4573512631:ℚ)/10000000000),((-30537375797349927682084160539758071218902197780611893908916397:ℚ)/120862052237268750000000000000000000000000000000000000000000000),((-5654548856973055100924759:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3469280809:ℚ)/5000000000),((1816667657:ℚ)/2500000000),((4549280809:ℚ)/7862500000),((20830008913:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2101474723:ℚ)/5000000000),((-12961648688140209492435478938484468069784734201789770164455159:ℚ)/52618939348242187500000000000000000000000000000000000000000000),((-347364027416808137425291:ℚ)/902500000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((7177778571:ℚ)/10000000000),((938227349:ℚ)/1250000000),((3112592857:ℚ)/5400000000),((10684046141:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3348958411:ℚ)/10000000000),((-117407574167339157770825619762179558368158023090331256957:ℚ)/478826065722656250000000000000000000000000000000000000000),((-171436469245059256134143:ℚ)/451250000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((463555863:ℚ)/625000000),((4708081961:ℚ)/5000000000),((598555863:ℚ)/1250000000),((51332737649:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((43991173:ℚ)/200000000),((-932311457641010237379932443509873519034012214799840479207:ℚ)/5101833600000000000000000000000000000000000000000000000000),((-76062098477517:ℚ)/200000000000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((582939543:ℚ)/625000000),((13228267867:ℚ)/10000000000),((239313181:ℚ)/575000000),((136974410803:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1418540252200622414892211000458064093487126954436881305921189:ℚ)/10156800000000000000000000000000000000000000000000000000000000),((-613421:ℚ)/1600000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC25
#check @N11Formalization.C450Source29GroupedC25.bound
#print axioms N11Formalization.C450Source29GroupedC25.valid0
#print axioms N11Formalization.C450Source29GroupedC25.valid1
#print axioms N11Formalization.C450Source29GroupedC25.valid2
#print axioms N11Formalization.C450Source29GroupedC25.valid3
#print axioms N11Formalization.C450Source29GroupedC25.valid4
#print axioms N11Formalization.C450Source29GroupedC25.valid5
#print axioms N11Formalization.C450Source29GroupedC25.valid6
#print axioms N11Formalization.C450Source29GroupedC25.valid7
#print axioms N11Formalization.C450Source29GroupedC25.valid8
#print axioms N11Formalization.C450Source29GroupedC25.valid9
#print axioms N11Formalization.C450Source29GroupedC25.valid10
#print axioms N11Formalization.C450Source29GroupedC25.valid11
#print axioms N11Formalization.C450Source29GroupedC25.valid12
#print axioms N11Formalization.C450Source29GroupedC25.bound
#print axioms N11Formalization.C450Source29GroupedC25.endpoint_checks
