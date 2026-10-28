import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((2918595889:ℚ)/5000000000),((49763707:ℚ)/78125000),((9555787667:ℚ)/13350000000),((701928191:ℚ)/775000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((868754201:ℚ)/1250000000),((-20106869617410632569818481804589249:ℚ)/660908437500000000000000000000000000),((-164362253306002495023170453:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3156284903:ℚ)/5000000000),((825929357:ℚ)/1250000000),((10268854709:ℚ)/13825000000),((3872360547:ℚ)/4450000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5906097381:ℚ)/10000000000),((-36174332375546282438393750399075357526527561629317323:ℚ)/1032180035400390625000000000000000000000000000000000000),((-163814817790223452450942437:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((6550239317:ℚ)/10000000000),((6845103221:ℚ)/10000000000),((21250717951:ℚ)/28600000000),((13718048839:ℚ)/15800000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5318436183:ℚ)/10000000000),((-321643722950540947647625738741067755684734841751145553:ℚ)/9138146875000000000000000000000000000000000000000000000),((-653009764529759765888588877:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1357579511:ℚ)/2000000000),((6963933273:ℚ)/10000000000),((4392738533:ℚ)/5815000000),((8870102959:ℚ)/10400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((933015613:ℚ)/2000000000),((-715724925895515706351263641797160545377986193343979:ℚ)/19202120935058593750000000000000000000000000000000000),((-26076848193087911354838853:ℚ)/118292480000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((863340349:ℚ)/1250000000),((3511673663:ℚ)/5000000000),((2790021047:ℚ)/3664062500),((49171757619:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((538058759:ℚ)/1250000000),((-26273710283378295238471974761934078786640183593347:ℚ)/686263060197234153747558593750000000000000000000000),((-10177779161547419719256093:ℚ)/46208000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((217691703:ℚ)/312500000),((28331043:ℚ)/40000000),((703075109:ℚ)/923437500),((396463559:ℚ)/469000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4113130357:ℚ)/10000000000),((-327112401784601739528617543606896496519418590263:ℚ)/8544370159506797790527343750000000000000000000000),((-1906689977326651650408011:ℚ)/8664000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((7025545609:ℚ)/10000000000),((178554339:ℚ)/250000000),((22676636827:ℚ)/29787500000),((2497206407:ℚ)/2955000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((391300361:ℚ)/1000000000),((-395240785993047854161010182071066759489428169761460301:ℚ)/10324337682342529296875000000000000000000000000000000000),((-650255986146713555244478533:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3542478073:ℚ)/5000000000),((1800396443:ℚ)/2500000000),((11427434219:ℚ)/15012500000),((25165153759:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1851330707:ℚ)/5000000000),((-3162115915945415377021682143208983889455511896873133:ℚ)/82603626298904418945312500000000000000000000000000000),((-162423821960188518459128997:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((178609153:ℚ)/250000000),((36304987:ℚ)/50000000),((575827459:ℚ)/756562500),((507164831:ℚ)/600500000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((696049589:ℚ)/2000000000),((-79939946194689139235020385464230818939056329913:ℚ)/2088379633426666259765625000000000000000000000000),((-405709219087112007936437:ℚ)/1848320000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((900471943:ℚ)/1250000000),((915051057:ℚ)/1250000000),((2901415829:ℚ)/3812500000),((12775663741:ℚ)/15131250000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3243276387:ℚ)/10000000000),((-13582714880066257730598090022608178759831610631743:ℚ)/354862213134765625000000000000000000000000000000000),((-10133974595708053730619557:ℚ)/46208000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((453949027:ℚ)/625000000),((1475963791:ℚ)/2000000000),((1461847081:ℚ)/1921093750),((20595529283:ℚ)/24400000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((2988280699:ℚ)/10000000000),((-13249874208806449244289244106721628707093876006701:ℚ)/346190961520187556743621826171875000000000000000000),((-2531305306455080689660197:ℚ)/11552000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1830648199:ℚ)/2500000000),((7439228909:ℚ)/10000000000),((841706371:ℚ)/1106250000),((103749975817:ℚ)/122950000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((42346453:ℚ)/156250000),((-2248741137121768456353080909640122198070419205173:ℚ)/58759403228759765625000000000000000000000000000000),((-40465881462726179100403493:ℚ)/184832000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((922750081:ℚ)/1250000000),((7558047231:ℚ)/10000000000),((2968250243:ℚ)/3931250000),((105294614003:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((600232391:ℚ)/2500000000),((-432825151732842833046395711079928992097524731083:ℚ)/11588362464681267738342285156250000000000000000000),((-10098673091900094498514773:ℚ)/46208000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((7500814861:ℚ)/10000000000),((3897838931:ℚ)/5000000000),((24102444583:ℚ)/32400000000),((54191906103:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((64694141:ℚ)/400000000),((-1947714248381291381357332560598053571959637936445507:ℚ)/54675000000000000000000000000000000000000000000000000),((-645945062045292212844227453:ℚ)/2957312000000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((1934609409:ℚ)/2500000000),((969649939:ℚ)/1000000000),((6203828227:ℚ)/10000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-447442349840259728213889767059157973859321221788149:ℚ)/24414062500000000000000000000000000000000000000000000),((-223676611:ℚ)/1024000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((9639209769:ℚ)/10000000000),((6748731769:ℚ)/5000000000),((30517629307:ℚ)/55200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-780749928857923814353578714881341:ℚ)/97336000000000000000000000000000000),((-223676611:ℚ)/1024000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC29
#check @N11Formalization.C450Source12GroupedC29.bound
#print axioms N11Formalization.C450Source12GroupedC29.valid0
#print axioms N11Formalization.C450Source12GroupedC29.valid1
#print axioms N11Formalization.C450Source12GroupedC29.valid2
#print axioms N11Formalization.C450Source12GroupedC29.valid3
#print axioms N11Formalization.C450Source12GroupedC29.valid4
#print axioms N11Formalization.C450Source12GroupedC29.valid5
#print axioms N11Formalization.C450Source12GroupedC29.valid6
#print axioms N11Formalization.C450Source12GroupedC29.valid7
#print axioms N11Formalization.C450Source12GroupedC29.valid8
#print axioms N11Formalization.C450Source12GroupedC29.valid9
#print axioms N11Formalization.C450Source12GroupedC29.valid10
#print axioms N11Formalization.C450Source12GroupedC29.valid11
#print axioms N11Formalization.C450Source12GroupedC29.valid12
#print axioms N11Formalization.C450Source12GroupedC29.valid13
#print axioms N11Formalization.C450Source12GroupedC29.valid14
#print axioms N11Formalization.C450Source12GroupedC29.valid15
#print axioms N11Formalization.C450Source12GroupedC29.bound
#print axioms N11Formalization.C450Source12GroupedC29.endpoint_checks
