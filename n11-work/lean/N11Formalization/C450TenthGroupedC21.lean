import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((3039030933:ℚ)/5000000000),((3293902557:ℚ)/5000000000),((3679030933:ℚ)/13350000000),((3869902557:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6439260181:ℚ)/10000000000),((213654792036383962446346299812149160179:ℚ)/17397928747008000000000000000000000000000),((-5801072508652197842812487:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6553734411:ℚ)/10000000000),((6825552569:ℚ)/10000000000),((7833734411:ℚ)/27650000000),((7977552569:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5309360759:ℚ)/10000000000),((612585551999615235309255135876784930487623928327778554347543:ℚ)/55879856187523200000000000000000000000000000000000000000000000),((-23847676789589475500543543:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((1358307191:ℚ)/2000000000),((6944420019:ℚ)/10000000000),((538102397:ℚ)/1875000000),((8096420019:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4654422753:ℚ)/10000000000),((129238205536207924082176379413232849582260438553941111:ℚ)/12424582800000000000000000000000000000000000000000000000),((-966821675972333108685023:ℚ)/9241600000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((3455214537:ℚ)/5000000000),((3501926133:ℚ)/5000000000),((4095214537:ℚ)/14181250000),((1359308711:ℚ)/3750000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((429276823:ℚ)/1000000000),((17210859262835981722370421172581930365274472707996564216659:ℚ)/1696847497558593750000000000000000000000000000000000000000000),((-6083067171044224180092527:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((6969873833:ℚ)/10000000000),((7063283561:ℚ)/10000000000),((8249873833:ℚ)/28600000000),((8215283561:ℚ)/22690000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((4100806747:ℚ)/10000000000),((602861235212198668679368151828187948884344828989828554261:ℚ)/59719418636985250000000000000000000000000000000000000000000),((-24413205776238808495198687:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((7029317431:ℚ)/10000000000),((890339241:ℚ)/1250000000),((2769772477:ℚ)/9612500000),((79564557:ℚ)/220000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1949985161:ℚ)/5000000000),((98872238253452484433109892924364807610810755854143993:ℚ)/9838768637500000000000000000000000000000000000000000000),((-24494192050890263001303263:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((7088759897:ℚ)/10000000000),((7182143389:ℚ)/10000000000),((8368759897:ℚ)/29075000000),((8334143389:ℚ)/23070000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1844402839:ℚ)/5000000000),((13847607505270122415134864095402600396388350846864111398427:ℚ)/1383951806726672250000000000000000000000000000000000000000000),((-24575227544703795719224447:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/4),((5:ℚ)/16),((7148201259:ℚ)/10000000000),((3620785983:ℚ)/5000000000),((8428201259:ℚ)/29312500000),((4196785983:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1732710553:ℚ)/5000000000),((5387232071229052278502898491774233571567587325444292185603:ℚ)/540635868543542187500000000000000000000000000000000000000000),((-24656312292986516368936823:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((900955193:ℚ)/1250000000),((7300999681:ℚ)/10000000000),((353651731:ℚ)/1231250000),((1207571383:ℚ)/3350000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((645455131:ℚ)/2000000000),((22627690918297088516365714675744937320621617488841423107:ℚ)/2279748294335937500000000000000000000000000000000000000000),((-386522598902747416537067:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((3633540389:ℚ)/5000000000),((3680213277:ℚ)/5000000000),((4273540389:ℚ)/14893750000),((1418737759:ℚ)/3940000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2970816909:ℚ)/10000000000),((64397337212399667691611420020828297963836394115182732027033:ℚ)/6512354333399550000000000000000000000000000000000000000000000),((-6204657421958796594648743:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3663259493:ℚ)/5000000000),((1483970521:ℚ)/2000000000),((4303259493:ℚ)/15012500000),((1714370521:ℚ)/4766000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2690808479:ℚ)/10000000000),((601031496278309376698363481022601794377175196838495833061:ℚ)/60996956149139646875000000000000000000000000000000000000000),((-6224965599662439958012967:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((7385956193:ℚ)/10000000000),((94233779:ℚ)/125000000),((8665956193:ℚ)/30500000000),((108633779:ℚ)/300250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2378943439:ℚ)/10000000000),((102790786100911750787445593803580683338130708192819:ℚ)/10319505826269531250000000000000000000000000000000000),((-24981144493790178364987567:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1500965539:ℚ)/2000000000),((3888196351:ℚ)/5000000000),((1756965539:ℚ)/6290000000),((4464196351:ℚ)/12200000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1584228241:ℚ)/10000000000),((11411633087693912337552098216819475676940129605258757206371:ℚ)/1122537372762500000000000000000000000000000000000000000000000),((-1005754278057249043722343:ℚ)/9241600000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7742559673:ℚ)/10000000000),((8014071907:ℚ)/10000000000),((3007519891:ℚ)/10800000000),((9166071907:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((729432019504889235964631806088407374404653145371599163463:ℚ)/72567047912400000000000000000000000000000000000000000000000),((-14002369:ℚ)/128000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((1995069507:ℚ)/2500000000),((198303977:ℚ)/200000000),((2315069507:ℚ)/10000000000),((221343977:ℚ)/518400000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2079605764809938072729439309753049112298530406031:ℚ)/163258675200000000000000000000000000000000000000000),((-14002369:ℚ)/128000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((98816511:ℚ)/100000000),((13716521303:ℚ)/10000000000),((111616511:ℚ)/552000000),((14868521303:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((643113347247866825016307461645873303169:ℚ)/39002112000000000000000000000000000000000),((-14002369:ℚ)/128000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
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
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC21
#check @N11Formalization.C450TenthGroupedC21.bound
#print axioms N11Formalization.C450TenthGroupedC21.valid0
#print axioms N11Formalization.C450TenthGroupedC21.valid1
#print axioms N11Formalization.C450TenthGroupedC21.valid2
#print axioms N11Formalization.C450TenthGroupedC21.valid3
#print axioms N11Formalization.C450TenthGroupedC21.valid4
#print axioms N11Formalization.C450TenthGroupedC21.valid5
#print axioms N11Formalization.C450TenthGroupedC21.valid6
#print axioms N11Formalization.C450TenthGroupedC21.valid7
#print axioms N11Formalization.C450TenthGroupedC21.valid8
#print axioms N11Formalization.C450TenthGroupedC21.valid9
#print axioms N11Formalization.C450TenthGroupedC21.valid10
#print axioms N11Formalization.C450TenthGroupedC21.valid11
#print axioms N11Formalization.C450TenthGroupedC21.valid12
#print axioms N11Formalization.C450TenthGroupedC21.valid13
#print axioms N11Formalization.C450TenthGroupedC21.valid14
#print axioms N11Formalization.C450TenthGroupedC21.valid15
#print axioms N11Formalization.C450TenthGroupedC21.bound
#print axioms N11Formalization.C450TenthGroupedC21.endpoint_checks
