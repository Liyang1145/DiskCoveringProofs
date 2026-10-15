import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((308654201:ℚ)/500000000),((3242133389:ℚ)/5000000000),((917866611:ℚ)/25750000000),((555345799:ℚ)/4960000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((778501013:ℚ)/1250000000),((42252003547809517744055018981043441313:ℚ)/323637984256000000000000000000000000000),((-8893222267508975220743799:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((6414118191:ℚ)/10000000000),((1681191243:ℚ)/2500000000),((398808757:ℚ)/13350000000),((10865881809:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1132335027:ℚ)/2000000000),((27482694164325054651818967745692532900281278244065608695069:ℚ)/211315687670898437500000000000000000000000000000000000000000),((-3758141134735030072756355719:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((415930977:ℚ)/625000000),((1368986807:ℚ)/2000000000),((295013193:ℚ)/10870000000),((221356341:ℚ)/2225000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1260070827:ℚ)/2500000000),((10459634752271766145206413422717182632127373422628364700441:ℚ)/81344679332128906250000000000000000000000000000000000000000),((-15466344120748986051879271:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((6775196719:ℚ)/10000000000),((1393010699:ℚ)/2000000000),((270989301:ℚ)/11060000000),((10504803281:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2351049007:ℚ)/5000000000),((59173523344635491443291326715601760397572630380390261974577887:ℚ)/460277964969055078125000000000000000000000000000000000000000000),((-11246977115567713494463599:ℚ)/40960000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((3447721751:ℚ)/5000000000),((3542562961:ℚ)/5000000000),((617437039:ℚ)/28125000000),((5192278249:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2169950079:ℚ)/5000000000),((524186276953736952283962510351695883621021741323036401369:ℚ)/4076816231250000000000000000000000000000000000000000000000),((-1040259664048905334259906199:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((17539097:ℚ)/25000000),((7205153711:ℚ)/10000000000),((1114846289:ℚ)/57200000000),((25660903:ℚ)/281250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((394704153:ℚ)/1000000000),((365745307036538949102021364721309750492444369130374443:ℚ)/2843345832824707031250000000000000000000000000000000000),((-26637662583757279214391:ℚ)/92416000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7135785239:ℚ)/10000000000),((1465027819:ℚ)/2000000000),((198972181:ℚ)/11630000000),((10144214761:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1756602313:ℚ)/5000000000),((1221885233230951936565944892750223909295542536975504805754044023:ℚ)/9492460170679200000000000000000000000000000000000000000000000000),((-4363122828093331934201789079:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7255885269:ℚ)/10000000000),((7445084161:ℚ)/10000000000),((291638613:ℚ)/19700000000),((10024114731:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3020732609:ℚ)/10000000000),((12290094244622440774137725132411943088530447672594731931644559:ℚ)/95387534255192187500000000000000000000000000000000000000000000),((-4464330982836895092854801839:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((7375941179:ℚ)/10000000000),((384243051:ℚ)/500000000),((31756949:ℚ)/3050000000),((9904058821:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2434232227:ℚ)/10000000000),((14973032777558195846842480575285870999480721590314030759989547:ℚ)/115216153378650000000000000000000000000000000000000000000000000),((-4565652236558937761447790159:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((237997783:ℚ)/312500000),((2041002241:ℚ)/2500000000),((12999253:ℚ)/5400000000),((302002217:ℚ)/3812500000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2777152282611242132749118589616896730416962638179064111:ℚ)/21040490341186523437500000000000000000000000000000000000),((-13172157:ℚ)/40960000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((80954609:ℚ)/100000000),((10077425511:ℚ)/10000000000),((-1757425511:ℚ)/64800000000),((91845391:ℚ)/1296000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((363693082135185737773119238778946705818269342787873:ℚ)/2550916800000000000000000000000000000000000000000000),((-13172157:ℚ)/40960000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((10009238087:ℚ)/10000000000),((6946668283:ℚ)/5000000000),((-2786668283:ℚ)/40000000000),((7270761913:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((172302867848330484053608910879827232271:ℚ)/1024000000000000000000000000000000000000),((-13172157:ℚ)/40960000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC15
#check @N11Formalization.C450Source28GroupedC15.bound
#print axioms N11Formalization.C450Source28GroupedC15.valid0
#print axioms N11Formalization.C450Source28GroupedC15.valid1
#print axioms N11Formalization.C450Source28GroupedC15.valid2
#print axioms N11Formalization.C450Source28GroupedC15.valid3
#print axioms N11Formalization.C450Source28GroupedC15.valid4
#print axioms N11Formalization.C450Source28GroupedC15.valid5
#print axioms N11Formalization.C450Source28GroupedC15.valid6
#print axioms N11Formalization.C450Source28GroupedC15.valid7
#print axioms N11Formalization.C450Source28GroupedC15.valid8
#print axioms N11Formalization.C450Source28GroupedC15.valid9
#print axioms N11Formalization.C450Source28GroupedC15.valid10
#print axioms N11Formalization.C450Source28GroupedC15.valid11
#print axioms N11Formalization.C450Source28GroupedC15.bound
#print axioms N11Formalization.C450Source28GroupedC15.endpoint_checks
