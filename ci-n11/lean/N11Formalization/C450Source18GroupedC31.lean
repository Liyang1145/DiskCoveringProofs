import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5557982727:ℚ)/10000000000),((3053902557:ℚ)/5000000000),((44025879089:ℚ)/53400000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((750550499:ℚ)/1000000000),((-180921917971605002913580829536756812797:ℚ)/1903416300000000000000000000000000000000),((-30990655390397385746851153:ℚ)/92416000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6033304391:ℚ)/10000000000),((6345552569:ℚ)/10000000000),((47353130737:ℚ)/55300000000),((21212657707:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((408545361:ℚ)/625000000),((-2175122034857440843451943785977382413849121177017447367:ℚ)/20068715625000000000000000000000000000000000000000000000),((-30579224252684460004091217:ℚ)/92416000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((6270948629:ℚ)/10000000000),((6583283561:ℚ)/10000000000),((49016640403:ℚ)/57200000000),((21925850683:ℚ)/22120000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((6003732237:ℚ)/10000000000),((-63422104884983908688006095276659206136448695455346150201:ℚ)/584841400000000000000000000000000000000000000000000000000),((-30165089076404402517480537:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3254291639:ℚ)/5000000000),((6702143389:ℚ)/10000000000),((25340041473:ℚ)/29075000000),((22282430167:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5425544757:ℚ)/10000000000),((-8794873732639623476989762719600070972200948810691302539:ℚ)/76808483740234375000000000000000000000000000000000000000),((-7489924010990174156281297:ℚ)/23104000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((66273973:ℚ)/100000000),((6820999681:ℚ)/10000000000),((171705937:ℚ)/197000000),((22638999043:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5114699673:ℚ)/10000000000),((-683383184702520480707797494403255660121512157139:ℚ)/5972947656250000000000000000000000000000000000000),((-2975274895753117557553:ℚ)/9241600000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3373104631:ℚ)/5000000000),((1387970521:ℚ)/2000000000),((26171732417:ℚ)/30025000000),((4599111563:ℚ)/4728000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2392798389:ℚ)/5000000000),((-7253111816293567359992272098186686890438526112914238817:ℚ)/63439584997558593750000000000000000000000000000000000000),((-7386459398882955531492177:ℚ)/23104000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3432509631:ℚ)/5000000000),((3499638927:ℚ)/5000000000),((26587567417:ℚ)/30262500000),((11586916781:ℚ)/12010000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((886829063:ℚ)/2000000000),((-7612464694243535011546929435600184764885515140067684417:ℚ)/64956960118103027343750000000000000000000000000000000000),((-7360813403467153263262177:ℚ)/23104000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((1384884711:ℚ)/2000000000),((88233779:ℚ)/125000000),((10718192977:ℚ)/12200000000),((291901337:ℚ)/302625000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((849662193:ℚ)/2000000000),((-1993943999202412341952078453141250177548981949870624057:ℚ)/17023575000000000000000000000000000000000000000000000000),((-61768057942217892319563:ℚ)/194560000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((109122303:ℚ)/156250000),((355906301:ℚ)/500000000),((843856121:ℚ)/960546875),((1176518903:ℚ)/1220000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((4054508593:ℚ)/10000000000),((-81055131198371632668777217742807101724856933609203:ℚ)/692381923040375113487243652343750000000000000000000),((-57102363728306774500779:ℚ)/180500000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3521615391:ℚ)/5000000000),((1794387243:ℚ)/2500000000),((27211307737:ℚ)/30975000000),((5927161729:ℚ)/6147500000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((3851531837:ℚ)/10000000000),((-10866786826890537256075843109981522696232141201659133011:ℚ)/92871822216796875000000000000000000000000000000000000000),((-7283250425314732153605217:ℚ)/23104000000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((7102633737:ℚ)/10000000000),((3648196351:ℚ)/5000000000),((54838436159:ℚ)/62900000000),((12032589053:ℚ)/12390000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3637841411:ℚ)/10000000000),((-66570068763803687975777450483736616123049371566540586759:ℚ)/583261380468750000000000000000000000000000000000000000000),((-28925315164375368688523633:ℚ)/92416000000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((361071919:ℚ)/500000000),((7415233639:ℚ)/10000000000),((2783503433:ℚ)/3192500000),((24421700917:ℚ)/25160000000),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((792384377:ℚ)/2500000000),((-725015188784117465250854502081008286252150382273611:ℚ)/6355105386352539062500000000000000000000000000000000),((-71796360231620675111977:ℚ)/231040000000000000000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((1468048279:ℚ)/2000000000),((7534071907:ℚ)/10000000000),((11300337953:ℚ)/12960000000),((24778215721:ℚ)/25540000000),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2622031889:ℚ)/10000000000),((-258585255666834799680445582963747065594198372003021217:ℚ)/2267481600000000000000000000000000000000000000000000000),((-1140472300719523158165937:ℚ)/3696640000000000000000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((1491808571:ℚ)/2000000000),((424234729:ℚ)/500000000),((11466659997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((1928969149:ℚ)/10000000000),((-49099639535574916273926469555551546338530321149444599:ℚ)/592974100000000000000000000000000000000000000000000000),((-1135918395662822078577337:ℚ)/3696640000000000000000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((8409405891:ℚ)/10000000000),((188703977:ℚ)/200000000),((63985841237:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-34321592574166264958731075148288083610146048391134001079:ℚ)/400000000000000000000000000000000000000000000000000000000),((-19667731:ℚ)/64000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((4679849959:ℚ)/5000000000),((13236521303:ℚ)/10000000000),((35318949713:ℚ)/55200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-628550894907179520539308883286447113:ℚ)/21024576000000000000000000000000000000),((-19667731:ℚ)/64000000)⟩
theorem valid15 : Valid source18 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((61:ℚ)/80) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((1239:ℚ)/1600) ((1277:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((1277:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source18 nn0 nn1 Qcell ((1277:ℚ)/1600) ((181:ℚ)/200) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source18 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source18 nn0 nn1 Qcell ((1277:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC31
#check @N11Formalization.C450Source18GroupedC31.bound
#print axioms N11Formalization.C450Source18GroupedC31.valid0
#print axioms N11Formalization.C450Source18GroupedC31.valid1
#print axioms N11Formalization.C450Source18GroupedC31.valid2
#print axioms N11Formalization.C450Source18GroupedC31.valid3
#print axioms N11Formalization.C450Source18GroupedC31.valid4
#print axioms N11Formalization.C450Source18GroupedC31.valid5
#print axioms N11Formalization.C450Source18GroupedC31.valid6
#print axioms N11Formalization.C450Source18GroupedC31.valid7
#print axioms N11Formalization.C450Source18GroupedC31.valid8
#print axioms N11Formalization.C450Source18GroupedC31.valid9
#print axioms N11Formalization.C450Source18GroupedC31.valid10
#print axioms N11Formalization.C450Source18GroupedC31.valid11
#print axioms N11Formalization.C450Source18GroupedC31.valid12
#print axioms N11Formalization.C450Source18GroupedC31.valid13
#print axioms N11Formalization.C450Source18GroupedC31.valid14
#print axioms N11Formalization.C450Source18GroupedC31.valid15
#print axioms N11Formalization.C450Source18GroupedC31.bound
#print axioms N11Formalization.C450Source18GroupedC31.endpoint_checks
