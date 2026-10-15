import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((6091242811:ℚ)/10000000000),((6597424599:ℚ)/10000000000),((19873728433:ℚ)/53400000000),((50021972193:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6410315119:ℚ)/10000000000),((542764288946860283798543:ℚ)/142578000000000000000000000),((-18136983625683095033541107:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6566510321:ℚ)/10000000000),((3417506559:ℚ)/5000000000),((21299530963:ℚ)/55300000000),((8614181971:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5276066513:ℚ)/10000000000),((49358770612968670825833198989553063628768411804867184130047:ℚ)/16168939869075000000000000000000000000000000000000000000000000),((-18396238731529295856345547:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((6804130279:ℚ)/10000000000),((6953805133:ℚ)/10000000000),((22012390837:ℚ)/56250000000),((52516635931:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4617363457:ℚ)/10000000000),((133093573730220190746517955151540140752020283918960432307:ℚ)/48921794775000000000000000000000000000000000000000000000000),((-18527530191480752301737147:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((6922937217:ℚ)/10000000000),((7013200613:ℚ)/10000000000),((22368811651:ℚ)/56725000000),((52932404291:ℚ)/112500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4253053421:ℚ)/10000000000),((58744873372903042900576688730660655699335436255054015290532469:ℚ)/22907441217041015625000000000000000000000000000000000000000000000),((-18593592069086574760613163:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((698233997:ℚ)/1000000000),((884074469:ℚ)/1250000000),((2254701991:ℚ)/5720000000),((6668521283:ℚ)/14181250000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((202973381:ℚ)/500000000),((152970652401101558444313645879136279347696265155719507:ℚ)/60247670209381103515625000000000000000000000000000000000),((-186267270632671414070803:ℚ)/2310400000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((3520871131:ℚ)/5000000000),((44574941:ℚ)/62500000),((11362613393:ℚ)/28837500000),((336024587:ℚ)/715000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((192837081:ℚ)/500000000),((1274024969512115626658371351820649334345784757255156359:ℚ)/506619719451269531250000000000000000000000000000000000000),((-4664982858650185459211587:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((887643013:ℚ)/1250000000),((7191385043:ℚ)/10000000000),((2862929039:ℚ)/7268750000),((54179695301:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3643346061:ℚ)/10000000000),((215515156265349501224093216727091537608495791100690019954633:ℚ)/86496987920417015625000000000000000000000000000000000000000000),((-292081331056784746736023:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/8),((7:ℚ)/16),((1790136377:ℚ)/2500000000),((7250779211:ℚ)/10000000000),((5770409131:ℚ)/14656250000),((54595454477:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((854319643:ℚ)/2500000000),((2002655911018478940113585168959031718297808025926840329400681:ℚ)/810953802815313281250000000000000000000000000000000000000000000),((-1170409270470495671659843:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((7219946483:ℚ)/10000000000),((7310173071:ℚ)/10000000000),((23259839449:ℚ)/59100000000),((55011211497:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3175829803:ℚ)/10000000000),((1076958341060537952161339991428228338167173788756045262492527:ℚ)/439848936538439941406250000000000000000000000000000000000000000),((-18759960857809252499174563:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((45495919:ℚ)/62500000),((736956663:ℚ)/1000000000),((146487757:ℚ)/372343750),((1847565547:ℚ)/3940000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2915175657:ℚ)/10000000000),((7907506161690506577729751288748831093805098784975302375471:ℚ)/3256177166699775000000000000000000000000000000000000000000000),((-367059429358911893881:ℚ)/4512500000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((733874719:ℚ)/1000000000),((1485791979:ℚ)/2000000000),((2361624157:ℚ)/6005000000),((11168543853:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1314803021:ℚ)/5000000000),((9185569069147353148246049152417480249255030758551620199427:ℚ)/3812309759321227929687500000000000000000000000000000000000000),((-188269941083787278608187:ℚ)/2310400000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((7398146941:ℚ)/10000000000),((7547745571:ℚ)/10000000000),((23794440823:ℚ)/61000000000),((56674218997:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((577473179:ℚ)/2500000000),((50036305668846253984842742611541131291667975859292993307363:ℚ)/20143675372878125000000000000000000000000000000000000000000000),((-18860614836518061808865027:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((7516945287:ℚ)/10000000000),((7785313689:ℚ)/10000000000),((24150835861:ℚ)/62900000000),((58337195823:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((739872097:ℚ)/5000000000),((1473380203654485279761998849911405323320865580807550855560057:ℚ)/561268686381250000000000000000000000000000000000000000000000000),((-18928064519321428910044923:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((1550907519:ℚ)/2000000000),((8022877811:ℚ)/10000000000),((4972722557:ℚ)/12960000000),((60000144677:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((104514752786297861423923915893287770971748251480539098001227:ℚ)/40818964450725000000000000000000000000000000000000000000000000),((-10512679:ℚ)/128000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((7992124487:ℚ)/10000000000),((1984656221:ℚ)/2000000000),((25576373461:ℚ)/80000000000),((14660593547:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((10277685044018678860991445903103951:ℚ)/2400000000000000000000000000000000000),((-10512679:ℚ)/128000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((19321623:ℚ)/19531250),((548950179:ℚ)/400000000),((61089869:ℚ)/215625000),((3996251253:ℚ)/6400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((14563196434026997007:ℚ)/2324707031250000000000),((-10512679:ℚ)/128000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC23
#check @N11Formalization.C450SeventhGroupedC23.bound
#print axioms N11Formalization.C450SeventhGroupedC23.valid0
#print axioms N11Formalization.C450SeventhGroupedC23.valid1
#print axioms N11Formalization.C450SeventhGroupedC23.valid2
#print axioms N11Formalization.C450SeventhGroupedC23.valid3
#print axioms N11Formalization.C450SeventhGroupedC23.valid4
#print axioms N11Formalization.C450SeventhGroupedC23.valid5
#print axioms N11Formalization.C450SeventhGroupedC23.valid6
#print axioms N11Formalization.C450SeventhGroupedC23.valid7
#print axioms N11Formalization.C450SeventhGroupedC23.valid8
#print axioms N11Formalization.C450SeventhGroupedC23.valid9
#print axioms N11Formalization.C450SeventhGroupedC23.valid10
#print axioms N11Formalization.C450SeventhGroupedC23.valid11
#print axioms N11Formalization.C450SeventhGroupedC23.valid12
#print axioms N11Formalization.C450SeventhGroupedC23.valid13
#print axioms N11Formalization.C450SeventhGroupedC23.valid14
#print axioms N11Formalization.C450SeventhGroupedC23.valid15
#print axioms N11Formalization.C450SeventhGroupedC23.bound
#print axioms N11Formalization.C450SeventhGroupedC23.endpoint_checks
