import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((742727239:ℚ)/1250000000),((3233002589:ℚ)/5000000000),((842727239:ℚ)/1668750000),((32617023301:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6732198153:ℚ)/10000000000),((-7081328207693877318735628103:ℚ)/2689243316650390625000000000000),((-8552202769980209717763753:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((1604394809:ℚ)/2500000000),((3351907309:ℚ)/5000000000),((257770687:ℚ)/493750000),((33687165781:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1130635907:ℚ)/2000000000),((-254130517552203747530338664403997180311093583561:ℚ)/47019863128662109375000000000000000000000000000000),((-34568140310239922637976233:ℚ)/184832000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((266216823:ℚ)/400000000),((1364542297:ℚ)/2000000000),((298216823:ℚ)/562500000),((13688880673:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((314928309:ℚ)/625000000),((-17127205150681000812718647292535803529948356363:ℚ)/2574920654296875000000000000000000000000000000000),((-889563030603816189121097:ℚ)/4731699200000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((338716629:ℚ)/500000000),((867700433:ℚ)/1250000000),((378716629:ℚ)/715000000),((8689303897:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2352303489:ℚ)/5000000000),((-87675183867564804563839193151142175466347806937:ℚ)/12980322265625000000000000000000000000000000000000),((-3860271714198758748233:ℚ)/20480000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((861654899:ℚ)/1250000000),((437565481:ℚ)/625000000),((320551633:ℚ)/600781250),((4378089329:ℚ)/7150000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((86935853:ℚ)/200000000),((-77576908107036234542767201447751501204656818377:ℚ)/10588127397932112216949462890625000000000000000000),((-8732368631492294279892193:ℚ)/46208000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((10863579:ℚ)/15625000),((1765122699:ℚ)/2500000000),((48454316:ℚ)/90859375),((17646104291:ℚ)/28837500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1039288123:ℚ)/2500000000),((-86310552650994337911921376897184643453645017:ℚ)/11720044516026973724365234375000000000000000000),((-1366202459972410312913:ℚ)/7220000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/2),((9:ℚ)/16),((3506070339:ℚ)/5000000000),((711993279:ℚ)/1000000000),((3906070339:ℚ)/7328125000),((7111939511:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1979497071:ℚ)/5000000000),((-40624756156083240106199919971287344259059061579291:ℚ)/5490104481577873229980468750000000000000000000000000),((-140080491939771103965161153:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((7071589577:ℚ)/10000000000),((3589686853:ℚ)/5000000000),((7871589577:ℚ)/14775000000),((5118168811:ℚ)/8375000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1875481949:ℚ)/5000000000),((-260126970972101851794773111900315617716677084780351:ℚ)/34997740173339843750000000000000000000000000000000000),((-561047913224533371479901897:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((1426207457:ℚ)/2000000000),((56553231:ℚ)/78125000),((1586207457:ℚ)/2978750000),((563979079:ℚ)/923437500),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1765656701:ℚ)/5000000000),((-77056214578850221794505143755154906830102511850671:ℚ)/10324337682342529296875000000000000000000000000000000),((-22470974572453190279238457:ℚ)/118292480000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((898810479:ℚ)/1250000000),((7298252403:ℚ)/10000000000),((998810479:ℚ)/1876562500),((72724271627:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3297717133:ℚ)/10000000000),((-1208772078496184133667165011425716491045177519493:ℚ)/161335207615047693252563476562500000000000000000000),((-8789083146175063633391513:ℚ)/46208000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((1812482311:ℚ)/2500000000),((3678845117:ℚ)/5000000000),((670827437:ℚ)/1260937500),((36629606053:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1523482321:ℚ)/5000000000),((-218090262072167560027526364332355012596642321573:ℚ)/29005272686481475830078125000000000000000000000000),((-35201799040248117797760553:ℚ)/184832000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((146187471:ℚ)/200000000),((3708563543:ℚ)/5000000000),((2658811:ℚ)/5000000),((36897071887:ℚ)/60525000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1387201483:ℚ)/5000000000),((-368342603688187439324022386627237248922317:ℚ)/48828125000000000000000000000000000000000000),((-225582701801241265866713:ℚ)/1182924800000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((294752671:ℚ)/400000000),((3767998969:ℚ)/5000000000),((15559651:ℚ)/29500000),((37431990721:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2472825367:ℚ)/10000000000),((-17857860543338470477236773296046935646997997:ℚ)/2507067871093750000000000000000000000000000000),((-903496369936092579897913:ℚ)/4731699200000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((93596251:ℚ)/125000000),((1530973027:ℚ)/2000000000),((103596251:ℚ)/196562500),((2169536749:ℚ)/3540000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((860605579:ℚ)/5000000000),((-20774646452202205497678885110921190083416013:ℚ)/2897090616170316934585571289062500000000000000),((-88459954102667305288593:ℚ)/462080000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((950822419:ℚ)/1250000000),((1578517841:ℚ)/2000000000),((1050822419:ℚ)/2025000000),((15614660569:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-85216773146503642339032902425290883824955514599:ℚ)/13348388671875000000000000000000000000000000000000),((-196510847:ℚ)/1024000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((3922163253:ℚ)/5000000000),((9793998201:ℚ)/10000000000),((4322163253:ℚ)/10000000000),((95185983809:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((13425921356053676293663909118027:ℚ)/6250000000000000000000000000000000),((-196510847:ℚ)/1024000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((9745880619:ℚ)/10000000000),((13595651491:ℚ)/10000000000),((10545880619:ℚ)/27600000000),((129400863419:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((61183811344319062937491:ℚ)/6348000000000000000000000),((-196510847:ℚ)/1024000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC25
#check @N11Formalization.C450Source12GroupedC25.bound
#print axioms N11Formalization.C450Source12GroupedC25.valid0
#print axioms N11Formalization.C450Source12GroupedC25.valid1
#print axioms N11Formalization.C450Source12GroupedC25.valid2
#print axioms N11Formalization.C450Source12GroupedC25.valid3
#print axioms N11Formalization.C450Source12GroupedC25.valid4
#print axioms N11Formalization.C450Source12GroupedC25.valid5
#print axioms N11Formalization.C450Source12GroupedC25.valid6
#print axioms N11Formalization.C450Source12GroupedC25.valid7
#print axioms N11Formalization.C450Source12GroupedC25.valid8
#print axioms N11Formalization.C450Source12GroupedC25.valid9
#print axioms N11Formalization.C450Source12GroupedC25.valid10
#print axioms N11Formalization.C450Source12GroupedC25.valid11
#print axioms N11Formalization.C450Source12GroupedC25.valid12
#print axioms N11Formalization.C450Source12GroupedC25.valid13
#print axioms N11Formalization.C450Source12GroupedC25.valid14
#print axioms N11Formalization.C450Source12GroupedC25.valid15
#print axioms N11Formalization.C450Source12GroupedC25.valid16
#print axioms N11Formalization.C450Source12GroupedC25.bound
#print axioms N11Formalization.C450Source12GroupedC25.endpoint_checks
