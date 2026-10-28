import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((1174454719:ℚ)/2000000000),((3204290339:ℚ)/5000000000),((4547364157:ℚ)/10680000000),((27870032373:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((275105477:ℚ)/400000000),((1216753762334001827686241:ℚ)/57031200000000000000000000),((-51517443746853584407955929:ℚ)/184832000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6349433971:ℚ)/10000000000),((6646991817:ℚ)/10000000000),((3452614559:ℚ)/7900000000),((57408942719:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((181825587:ℚ)/312500000),((15482819123625002781771963992520629:ℚ)/936150000000000000000000000000000000),((-211055564524633039165976161:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((411743883:ℚ)/625000000),((68853421:ℚ)/100000000),((1555231649:ℚ)/3575000000),((590773947:ℚ)/1106000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1043977767:ℚ)/2000000000),((78316827986699033642080774033497:ℚ)/4915625000000000000000000000000000),((-21329488625639233167609:ℚ)/73932800000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6826305599:ℚ)/10000000000),((7004496297:ℚ)/10000000000),((25598916797:ℚ)/58150000000),((59911474079:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1137857903:ℚ)/2500000000),((356346357063381112968878731078166299:ℚ)/25360668750000000000000000000000000000),((-215770836308576566602897441:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3472742537:ℚ)/5000000000),((1780909359:ℚ)/2500000000),((12978227611:ℚ)/29550000000),((15186365513:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2090283521:ℚ)/5000000000),((3366449615438664231165464378535289:ℚ)/242556250000000000000000000000000000),((-13554950812348260524545969:ℚ)/46208000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((1766162667:ℚ)/2500000000),((362138307:ℚ)/500000000),((6578488001:ℚ)/15012500000),((3078968149:ℚ)/5910000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1887903317:ℚ)/5000000000),((46420094232269506039554799621559669:ℚ)/3380627343750000000000000000000000000),((-544957917816239442837401:ℚ)/1848320000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((7183803047:ℚ)/10000000000),((7361882993:ℚ)/10000000000),((26671409141:ℚ)/61000000000),((62413180951:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3324756047:ℚ)/10000000000),((253147104048220263073313803860122683:ℚ)/18605000000000000000000000000000000000),((-219082706354723199156255601:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((730294283:ℚ)/1000000000),((58445223:ℚ)/78125000),((2702882849:ℚ)/6195000000),((494116561:ℚ)/953125000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((561026081:ℚ)/2000000000),((1295593894581596527608244509015527:ℚ)/95945062500000000000000000000000000),((-107508709862839713488493:ℚ)/361000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3711035301:ℚ)/5000000000),((7600083309:ℚ)/10000000000),((13693105903:ℚ)/31450000000),((64080583163:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((216811851:ℚ)/1000000000),((2074246770005674150493415634755839:ℚ)/154547265625000000000000000000000000),((-72785776180057833:ℚ)/243200000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((7541186909:ℚ)/10000000000),((3919121193:ℚ)/5000000000),((27743560727:ℚ)/64800000000),((32873848351:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1244874787:ℚ)/10000000000),((306424303676092167690763651894681051:ℚ)/20995200000000000000000000000000000000),((-146467656356884097:ℚ)/486400000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((7779387161:ℚ)/10000000000),((9742384487:ℚ)/10000000000),((28458161483:ℚ)/80000000000),((79076691409:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((661677759369065751165778671597525113:ℚ)/24000000000000000000000000000000000000),((-77321107:ℚ)/256000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((9683787803:ℚ)/10000000000),((13547240481:ℚ)/10000000000),((34171363409:ℚ)/110400000000),((105710683367:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((261191758024134594579539129:ℚ)/6094080000000000000000000000),((-77321107:ℚ)/256000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC23
#check @N11Formalization.C450Source18GroupedC23.bound
#print axioms N11Formalization.C450Source18GroupedC23.valid0
#print axioms N11Formalization.C450Source18GroupedC23.valid1
#print axioms N11Formalization.C450Source18GroupedC23.valid2
#print axioms N11Formalization.C450Source18GroupedC23.valid3
#print axioms N11Formalization.C450Source18GroupedC23.valid4
#print axioms N11Formalization.C450Source18GroupedC23.valid5
#print axioms N11Formalization.C450Source18GroupedC23.valid6
#print axioms N11Formalization.C450Source18GroupedC23.valid7
#print axioms N11Formalization.C450Source18GroupedC23.valid8
#print axioms N11Formalization.C450Source18GroupedC23.valid9
#print axioms N11Formalization.C450Source18GroupedC23.valid10
#print axioms N11Formalization.C450Source18GroupedC23.valid11
#print axioms N11Formalization.C450Source18GroupedC23.bound
#print axioms N11Formalization.C450Source18GroupedC23.endpoint_checks
