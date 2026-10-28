import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((97042821:ℚ)/156250000),((6720031933:ℚ)/10000000000),((-2880031933:ℚ)/49600000000),((32957179:ℚ)/1550000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1228511219:ℚ)/2000000000),((40027050736802157776690870199817:ℚ)/930968750000000000000000000000000),((-141682500791762195690341:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((1671823463:ℚ)/2500000000),((6839131981:ℚ)/10000000000),((-2999131981:ℚ)/53400000000),((408176537:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4951297109:ℚ)/10000000000),((14857067811533028480252270423513246514365386131686337051:ℚ)/356890556250000000000000000000000000000000000000000000000),((-42471035835586298325783069:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((3403199043:ℚ)/5000000000),((139164399:ℚ)/200000000),((-62364399:ℚ)/1087000000),((756800957:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2305330499:ℚ)/5000000000),((7798552617068839138740423883657260347954534202399480919:ℚ)/188139477978515625000000000000000000000000000000000000000),((-176083399465321844144830549:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((432843131:ℚ)/625000000),((7077296457:ℚ)/10000000000),((-3237296457:ℚ)/55300000000),((87156869:ℚ)/6912500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((530613111:ℚ)/1250000000),((12176243581037681508323296685040895747041040497825267:ℚ)/294908581542968750000000000000000000000000000000000000),((-2848161017947967145271461:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((3522285253:ℚ)/5000000000),((55756489:ℚ)/78125000),((-25756489:ℚ)/439453125),((637714747:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((240427319:ℚ)/625000000),((45685254895405341527907519115503839709769575771950957803:ℚ)/1112365722656250000000000000000000000000000000000000000000),((-188480892786703983243836709:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((7104106543:ℚ)/10000000000),((3598181037:ℚ)/5000000000),((-1678181037:ℚ)/28362500000),((1215893457:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1816195553:ℚ)/5000000000),((14967860600134140160039592011107648482115862295979763113:ℚ)/365050972156250000000000000000000000000000000000000000000),((-766320307147444260152625549:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((895454987:ℚ)/1250000000),((7255890969:ℚ)/10000000000),((-3415890969:ℚ)/57200000000),((144545013:ℚ)/14300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3405108017:ℚ)/10000000000),((187045047825014610664404701092840184716512761992762653:ℚ)/4569073437500000000000000000000000000000000000000000000),((-12167449530575681900980869:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((722317063:ℚ)/1000000000),((365770867:ℚ)/500000000),((-173770867:ℚ)/2883750000),((36560979:ℚ)/3845000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((395277039:ℚ)/1250000000),((580887705722976018191181597713647026388007394790091:ℚ)/14211144031250000000000000000000000000000000000000000),((-7911129730716116903496669:ℚ)/147865600000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7282698809:ℚ)/10000000000),((3717231377:ℚ)/5000000000),((-1797231377:ℚ)/29075000000),((1037301191:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2899791297:ℚ)/10000000000),((301465948756191021303015591258874664321624980509778430053:ℚ)/7373614439062500000000000000000000000000000000000000000000),((-803508929781356076754802781:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((3700873877:ℚ)/5000000000),((1888374697:ℚ)/2500000000),((-928374697:ℚ)/14775000000),((153042041:ℚ)/19700000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2289105903:ℚ)/10000000000),((5845164804971077044728070791339645784398630311578606067:ℚ)/143350743750000000000000000000000000000000000000000000000),((-207075039079339717809509829:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((3760393603:ℚ)/5000000000),((3836262941:ℚ)/5000000000),((-1916262941:ℚ)/30025000000),((399606397:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1445053089:ℚ)/10000000000),((55052219133764775160746068115402645645790609583077907517:ℚ)/1353377813281250000000000000000000000000000000000000000000),((-213272637050158585744164309:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((763981761:ℚ)/1000000000),((8148552749:ℚ)/10000000000),((-4308552749:ℚ)/61000000000),((68018239:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((116261582053401382816851682813845599288706434902406271:ℚ)/2837262500000000000000000000000000000000000000000000000),((-60220743:ℚ)/1024000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((8115820921:ℚ)/10000000000),((2010336477:ℚ)/2000000000),((-414112159:ℚ)/4320000000),((68059693:ℚ)/43200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3982881757460422519938280837514810950676861822943919511:ℚ)/94478400000000000000000000000000000000000000000000000000),((-60220743:ℚ)/1024000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((5009259203:ℚ)/5000000000),((13855352609:ℚ)/10000000000),((-10015352609:ℚ)/80000000000),((-283086401:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((10829697477783271673995131008641627563411496501451355197:ℚ)/233606400000000000000000000000000000000000000000000000000),((-60220743:ℚ)/1024000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC15
#check @N11Formalization.C450Source14GroupedC15.bound
#print axioms N11Formalization.C450Source14GroupedC15.valid0
#print axioms N11Formalization.C450Source14GroupedC15.valid1
#print axioms N11Formalization.C450Source14GroupedC15.valid2
#print axioms N11Formalization.C450Source14GroupedC15.valid3
#print axioms N11Formalization.C450Source14GroupedC15.valid4
#print axioms N11Formalization.C450Source14GroupedC15.valid5
#print axioms N11Formalization.C450Source14GroupedC15.valid6
#print axioms N11Formalization.C450Source14GroupedC15.valid7
#print axioms N11Formalization.C450Source14GroupedC15.valid8
#print axioms N11Formalization.C450Source14GroupedC15.valid9
#print axioms N11Formalization.C450Source14GroupedC15.valid10
#print axioms N11Formalization.C450Source14GroupedC15.valid11
#print axioms N11Formalization.C450Source14GroupedC15.valid12
#print axioms N11Formalization.C450Source14GroupedC15.valid13
#print axioms N11Formalization.C450Source14GroupedC15.bound
#print axioms N11Formalization.C450Source14GroupedC15.endpoint_checks
