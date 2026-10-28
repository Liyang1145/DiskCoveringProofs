import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/16),((1:ℚ)/8),((2979803271:ℚ)/5000000000),((1569779549:ℚ)/2500000000),((11619803271:ℚ)/51500000000),((3809779549:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1673642461:ℚ)/2500000000),((-51082388027953804441722603145713934553677125953521813451:ℚ)/853692968750000000000000000000000000000000000000000000000),((-33114358533256286583786473:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6200867939:ℚ)/10000000000),((6519895637:ℚ)/10000000000),((23480867939:ℚ)/106800000000),((15479895637:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((385316191:ℚ)/625000000),((-108275991046300415475478016103318939987568808688059494799:ℚ)/1903416300000000000000000000000000000000000000000000000000),((-544277688134719160623886937:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6441855739:ℚ)/10000000000),((1660049181:ℚ)/2500000000),((23721855739:ℚ)/108700000000),((3900049181:ℚ)/13350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((223730657:ℚ)/400000000),((-452749372733080370750000767459318077788673365771236311199:ℚ)/8027284393750000000000000000000000000000000000000000000000),((-105242490519853012886707259:ℚ)/346560000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((820282033:ℚ)/1250000000),((6760443507:ℚ)/10000000000),((2980282033:ℚ)/13825000000),((15720443507:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((165224179:ℚ)/312500000),((-42602586348405941485874064081682821245084331853517239:ℚ)/774135026550292968750000000000000000000000000000000000),((-1705129483844320975169847131:ℚ)/5544960000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((3341299467:ℚ)/5000000000),((1376127761:ℚ)/2000000000),((3993766489:ℚ)/18750000000),((3168127761:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4964282821:ℚ)/10000000000),((-25933305420866122387377728238886924087547354380715407:ℚ)/482797622680664062500000000000000000000000000000000000),((-23016248256223031939860033:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((3401443379:ℚ)/5000000000),((1750196311:ℚ)/2500000000),((12041443379:ℚ)/57200000000),((1330065437:ℚ)/4687500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((462103483:ℚ)/1000000000),((-61343339762340130932788881935968556741607036936842932319:ℚ)/1169682800000000000000000000000000000000000000000000000000),((-36398916587157416700678833:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((865390317:ℚ)/1250000000),((3560442637:ℚ)/5000000000),((3025390317:ℚ)/14537500000),((8040442637:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((850492479:ℚ)/2000000000),((-983508820260734154148375968803799311643655394288352417:ℚ)/19202120935058593750000000000000000000000000000000000000),((-147326525411283323062580937:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((1760827221:ℚ)/2500000000),((56569853:ℚ)/78125000),((2026942407:ℚ)/9850000000),((126569853:ℚ)/454296875),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3851258297:ℚ)/10000000000),((-74713886198125250249619963530934321518310520052467443:ℚ)/1493236914062500000000000000000000000000000000000000000),((-36387739872927681988757:ℚ)/112812500000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7163448241:ℚ)/10000000000),((7480929061:ℚ)/10000000000),((24443448241:ℚ)/122000000000),((5480309687:ℚ)/19700000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3405863031:ℚ)/10000000000),((-1602997015320856606136428555000991169228602921265193492543:ℚ)/34047150000000000000000000000000000000000000000000000000000),((-599917105171706116093587833:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7403594963:ℚ)/10000000000),((1592092181:ℚ)/2000000000),((24683594963:ℚ)/129600000000),((55476921:ℚ)/200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1139185009:ℚ)/5000000000),((-189598840880886941618886815543500533878803385410429866749:ℚ)/4534963200000000000000000000000000000000000000000000000000),((-5069871979945779:ℚ)/15200000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((7883415729:ℚ)/10000000000),((2468559523:ℚ)/2500000000),((25163415729:ℚ)/160000000000),((1569519841:ℚ)/5400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-629092291935623303284119173086001830148534925658811223309:ℚ)/25600000000000000000000000000000000000000000000000000000000),((-43808467:ℚ)/128000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((489903411:ℚ)/500000000),((13690339813:ℚ)/10000000000),((451301137:ℚ)/3680000000),((22650339813:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-642799925852864232140632124582271090986997770142799:ℚ)/233606400000000000000000000000000000000000000000000000),((-43808467:ℚ)/128000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC18
#check @N11Formalization.C450Source29GroupedC18.bound
#print axioms N11Formalization.C450Source29GroupedC18.valid0
#print axioms N11Formalization.C450Source29GroupedC18.valid1
#print axioms N11Formalization.C450Source29GroupedC18.valid2
#print axioms N11Formalization.C450Source29GroupedC18.valid3
#print axioms N11Formalization.C450Source29GroupedC18.valid4
#print axioms N11Formalization.C450Source29GroupedC18.valid5
#print axioms N11Formalization.C450Source29GroupedC18.valid6
#print axioms N11Formalization.C450Source29GroupedC18.valid7
#print axioms N11Formalization.C450Source29GroupedC18.valid8
#print axioms N11Formalization.C450Source29GroupedC18.valid9
#print axioms N11Formalization.C450Source29GroupedC18.valid10
#print axioms N11Formalization.C450Source29GroupedC18.valid11
#print axioms N11Formalization.C450Source29GroupedC18.bound
#print axioms N11Formalization.C450Source29GroupedC18.endpoint_checks
