import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((6225425729:ℚ)/10000000000),((6721831397:ℚ)/10000000000),((-16325494191:ℚ)/99200000000),((-1328475243:ℚ)/17800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3054475079:ℚ)/5000000000),((4050024546005031983857488615756016297140863278188824899:ℚ)/273175487500000000000000000000000000000000000000000000000),((237398341213156424415400843:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((3350375727:ℚ)/5000000000),((3420340281:ℚ)/5000000000),((-2780340281:ℚ)/17800000000),((-2230375727:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((491390029:ℚ)/1000000000),((159039330852818168979233555352488023137293733039668347089:ℚ)/11162942360058593750000000000000000000000000000000000000000),((52867323181456139823926547:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3409787881:ℚ)/5000000000),((1739881579:ℚ)/2500000000),((-4259644737:ℚ)/27175000000),((-2289787881:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((228576709:ℚ)/500000000),((31857621660911806112193331507230530846305057033064243481:ℚ)/2243959396960449218750000000000000000000000000000000000000),((12840989773448484360440107:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((3469198757:ℚ)/5000000000),((7018947969:ℚ)/10000000000),((-217934733:ℚ)/1400000000),((-2349198757:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4203478607:ℚ)/10000000000),((836237229145283237007868455984861500263946805114557373:ℚ)/59304387464141845703125000000000000000000000000000000000),((199136034802838398259308547:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((6997807473:ℚ)/10000000000),((110599513:ℚ)/156250000),((-271798539:ℚ)/1742968750),((-4757807473:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4007616123:ℚ)/10000000000),((409467552618249160756569324296243992123727982388469811067:ℚ)/29082280397415161132812500000000000000000000000000000000000),((2520252147676798960827:ℚ)/190000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((7057216841:ℚ)/10000000000),((7137788927:ℚ)/10000000000),((-1952596309:ℚ)/12500000000),((-4817216841:ℚ)/56725000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1901124889:ℚ)/5000000000),((40096716406528084647123881071659719979615305332238183:ℚ)/2851960719970703125000000000000000000000000000000000000),((193138874067470481472065283:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((222394551:ℚ)/312500000),((449825517:ℚ)/625000000),((-1109476551:ℚ)/7090625000),((-152394551:ℚ)/1787500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((358574301:ℚ)/1000000000),((1137149134239443063675300379414433677899017466695312293:ℚ)/80993965856933593750000000000000000000000000000000000000),((742751354670338822182203:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((7176033863:ℚ)/10000000000),((1451325377:ℚ)/2000000000),((-3585976131:ℚ)/22880000000),((-1645344621:ℚ)/19225000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3355936121:ℚ)/10000000000),((3478276049258360663290972590298113550959323864787309:ℚ)/248070507381439208984375000000000000000000000000000000),((7486100814948053525226883:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((1447088309:ℚ)/2000000000),((1463208957:ℚ)/2000000000),((-1207208957:ℚ)/7690000000),((-999088309:ℚ)/11630000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((62197551:ℚ)/200000000),((105872371946696566679443852079374815074206783561367168963:ℚ)/7560412671518750000000000000000000000000000000000000000000),((7366535767761314239383323:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-3:ℚ)/16),((-1:ℚ)/8),((7294848693:ℚ)/10000000000),((737546199:ℚ)/1000000000),((-1828638597:ℚ)/11630000000),((-5054848693:ℚ)/58625000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2843346363:ℚ)/10000000000),((61452342332135273600810851095043756561351173095888288669299:ℚ)/4393691439221191406250000000000000000000000000000000000000000),((95356298643883878532833:ℚ)/7782400000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((7354255319:ℚ)/10000000000),((1486975703:ℚ)/2000000000),((-3692927109:ℚ)/23450000000),((-1704751773:ℚ)/19700000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((637481389:ℚ)/2500000000),((78269966301878321137034411192262127279314672471675293311:ℚ)/5602624901562500000000000000000000000000000000000000000000),((7127729575294858966821043:ℚ)/591462400000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7413661437:ℚ)/10000000000),((944213699:ℚ)/1250000000),((-784213699:ℚ)/4925000000),((-5173661437:ℚ)/60050000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2218967459:ℚ)/10000000000),((2799557486826680022157002972648224127304998853895009630341:ℚ)/199961571912304687500000000000000000000000000000000000000000),((2742980191723098610828827:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((3766236097:ℚ)/5000000000),((3836269071:ℚ)/5000000000),((-9588807213:ℚ)/60050000000),((-2646236097:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((166756061:ℚ)/1250000000),((2975345280237728615256297260944682255072432563872503303671:ℚ)/212972016406250000000000000000000000000000000000000000000000),((1391304637444669:ℚ)/121600000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((3825640529:ℚ)/5000000000),((8147829289:ℚ)/10000000000),((-20603487867:ℚ)/122000000000),((-2705640529:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((61374902221098104611808260661446181887685633663728294601:ℚ)/4322386800000000000000000000000000000000000000000000000000),((2291029:ℚ)/204800000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((8126499241:ℚ)/10000000000),((10048717099:ℚ)/10000000000),((-8768717099:ℚ)/43200000000),((-5886499241:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((431166516272399872798077711078248309299004218392974123663:ℚ)/28800000000000000000000000000000000000000000000000000000000),((2291029:ℚ)/204800000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((2506791149:ℚ)/2500000000),((2769951803:ℚ)/2000000000),((-7541855409:ℚ)/32000000000),((-648930383:ℚ)/9200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((60290166507750421969856787153170145510177574547824747:ℚ)/3650100000000000000000000000000000000000000000000000000),((2291029:ℚ)/204800000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC14
#check @N11Formalization.C450EighthGroupedC14.bound
#print axioms N11Formalization.C450EighthGroupedC14.valid0
#print axioms N11Formalization.C450EighthGroupedC14.valid1
#print axioms N11Formalization.C450EighthGroupedC14.valid2
#print axioms N11Formalization.C450EighthGroupedC14.valid3
#print axioms N11Formalization.C450EighthGroupedC14.valid4
#print axioms N11Formalization.C450EighthGroupedC14.valid5
#print axioms N11Formalization.C450EighthGroupedC14.valid6
#print axioms N11Formalization.C450EighthGroupedC14.valid7
#print axioms N11Formalization.C450EighthGroupedC14.valid8
#print axioms N11Formalization.C450EighthGroupedC14.valid9
#print axioms N11Formalization.C450EighthGroupedC14.valid10
#print axioms N11Formalization.C450EighthGroupedC14.valid11
#print axioms N11Formalization.C450EighthGroupedC14.valid12
#print axioms N11Formalization.C450EighthGroupedC14.valid13
#print axioms N11Formalization.C450EighthGroupedC14.valid14
#print axioms N11Formalization.C450EighthGroupedC14.valid15
#print axioms N11Formalization.C450EighthGroupedC14.bound
#print axioms N11Formalization.C450EighthGroupedC14.endpoint_checks
