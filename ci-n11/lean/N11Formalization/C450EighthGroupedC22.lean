import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((6089564147:ℚ)/10000000000),((824513201:ℚ)/1250000000),((6857564147:ℚ)/21360000000),((2753539603:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6414007659:ℚ)/10000000000),((27307018231660868932486939077990197057:ℚ)/4247541198000000000000000000000000000000),((-246296351667805651858058169:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((820618909:ℚ)/1250000000),((3416869743:ℚ)/5000000000),((11602771:ℚ)/35000000),((11370609229:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2640069799:ℚ)/5000000000),((96187575436632004004853254093813923931103116858264034151:ℚ)/17487637256250000000000000000000000000000000000000000000000),((-3923332982406047058047321:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((6802624861:ℚ)/10000000000),((6952553031:ℚ)/10000000000),((7570624861:ℚ)/22500000000),((23097659093:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((462180771:ℚ)/1000000000),((62351962957151244310888347720763283148282364561393143083:ℚ)/12230448693750000000000000000000000000000000000000000000000),((-253511108182383983287199961:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((6921457253:ℚ)/10000000000),((1752989751:ℚ)/2500000000),((7689457253:ℚ)/22690000000),((5818969253:ℚ)/14062500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4257770611:ℚ)/10000000000),((439413262266143795449239161930307680770041476024208357895141:ℚ)/89482192254066467285156250000000000000000000000000000000000000),((-254724841349252342110382569:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((6980872413:ℚ)/10000000000),((7071364463:ℚ)/10000000000),((7748872413:ℚ)/22880000000),((23454093389:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((7938193:ℚ)/19531250),((350140854058219803597865183493141200884799428021060339841:ℚ)/71778147400222656250000000000000000000000000000000000000000),((-765998751351734651709768587:ℚ)/8871936000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((3520143453:ℚ)/5000000000),((7130769419:ℚ)/10000000000),((1301381151:ℚ)/3845000000),((23632308257:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((30894631:ℚ)/80000000),((2514555433862483998765143232412829351484682926914361575361163:ℚ)/518778592718100000000000000000000000000000000000000000000000000),((-191956349409873527840263307:ℚ)/2217984000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((7099700747:ℚ)/10000000000),((3595086943:ℚ)/5000000000),((7867700747:ℚ)/23260000000),((11905260829:ℚ)/28837500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3648672139:ℚ)/10000000000),((13021832424451963605806519419348357991766116146954967909239:ℚ)/2703030872513031738281250000000000000000000000000000000000000),((-256551487763654549812114569:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/16),((3:ℚ)/8),((7159113953:ℚ)/10000000000),((57996623:ℚ)/80000000),((7927113953:ℚ)/23450000000),((191909869:ℚ)/465200000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3422894961:ℚ)/10000000000),((497142706048453280509312142633687782199345786555662111:ℚ)/103802086760360100000000000000000000000000000000000000000),((-257161982916743131482930769:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((360926327:ℚ)/500000000),((3654490699:ℚ)/5000000000),((399326327:ℚ)/1182000000),((12083472097:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1590903727:ℚ)/5000000000),((65462570690513217990390847739766769597430590138564204585169:ℚ)/13745279266826248168945312500000000000000000000000000000000000),((-644433212027735332440289:ℚ)/7393280000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((3638969261:ℚ)/5000000000),((3684192233:ℚ)/5000000000),((4022969261:ℚ)/11915000000),((12172576699:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((730404289:ℚ)/2500000000),((13014726402394316871213027650703889052178452496055949909233081:ℚ)/2747399484402935156250000000000000000000000000000000000000000000),((-64596348391407033893728761:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((7337349913:ℚ)/10000000000),((7427787089:ℚ)/10000000000),((8105349913:ℚ)/24020000000),((24523361267:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2636669633:ℚ)/10000000000),((561478378538576255533924500972685612129002876302954703727211:ℚ)/119134679978788372802734375000000000000000000000000000000000000),((-258998309300032363816854529:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((924595091:ℚ)/1250000000),((1886647761:ℚ)/2500000000),((1020595091:ℚ)/3050000000),((6219943283:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((579461561:ℚ)/2500000000),((377443090373900082122777977213707228571407506609689933859:ℚ)/78686231925305175781250000000000000000000000000000000000000),((-4056438002267150975315321:ℚ)/46208000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1878895171:ℚ)/2500000000),((7784194061:ℚ)/10000000000),((121817363:ℚ)/370000000),((25592582183:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((298374661:ℚ)/2000000000),((2406429926874754881570518869676200339830906749605631956471:ℚ)/485526545312500000000000000000000000000000000000000000000000),((-16302618727018459980502681:ℚ)/184832000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((7753214251:ℚ)/10000000000),((4010895517:ℚ)/5000000000),((8521214251:ℚ)/25920000000),((13152686551:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((6219347859876880597972435739063715230709213249064182747143:ℚ)/1275592639085156250000000000000000000000000000000000000000000),((-90622463:ℚ)/1024000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((7990839979:ℚ)/10000000000),((1984480183:ℚ)/2000000000),((8758839979:ℚ)/32000000000),((6401440549:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((17508653950524552640234436996195115373478641310098471:ℚ)/2550916800000000000000000000000000000000000000000000000),((-90622463:ℚ)/1024000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((247290767:ℚ)/250000000),((6861558361:ℚ)/5000000000),((266490767:ℚ)/1104000000),((21704675083:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5676059525417359591691:ℚ)/609408000000000000000000),((-90622463:ℚ)/1024000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC22
#check @N11Formalization.C450EighthGroupedC22.bound
#print axioms N11Formalization.C450EighthGroupedC22.valid0
#print axioms N11Formalization.C450EighthGroupedC22.valid1
#print axioms N11Formalization.C450EighthGroupedC22.valid2
#print axioms N11Formalization.C450EighthGroupedC22.valid3
#print axioms N11Formalization.C450EighthGroupedC22.valid4
#print axioms N11Formalization.C450EighthGroupedC22.valid5
#print axioms N11Formalization.C450EighthGroupedC22.valid6
#print axioms N11Formalization.C450EighthGroupedC22.valid7
#print axioms N11Formalization.C450EighthGroupedC22.valid8
#print axioms N11Formalization.C450EighthGroupedC22.valid9
#print axioms N11Formalization.C450EighthGroupedC22.valid10
#print axioms N11Formalization.C450EighthGroupedC22.valid11
#print axioms N11Formalization.C450EighthGroupedC22.valid12
#print axioms N11Formalization.C450EighthGroupedC22.valid13
#print axioms N11Formalization.C450EighthGroupedC22.valid14
#print axioms N11Formalization.C450EighthGroupedC22.valid15
#print axioms N11Formalization.C450EighthGroupedC22.bound
#print axioms N11Formalization.C450EighthGroupedC22.endpoint_checks
