import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((6021145977:ℚ)/10000000000),((817131239:ℚ)/1250000000),((19343437931:ℚ)/35600000000),((873131239:ℚ)/1240000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6562988557:ℚ)/10000000000),((-34328609401377589193447567260981471:ℚ)/11279504000000000000000000000000000000),((-135974241311784257000881523:ℚ)/1108992000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3248210193:ℚ)/5000000000),((3387325657:ℚ)/5000000000),((31153891737:ℚ)/55300000000),((1203775219:ℚ)/1780000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((43651689:ℚ)/80000000),((-4678149211763691002652837723645142113583513833774625359:ℚ)/1056952356250000000000000000000000000000000000000000000000),((-34181410160604403250788163:ℚ)/277248000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((6734043437:ℚ)/10000000000),((1378689889:ℚ)/2000000000),((21482130311:ℚ)/37500000000),((1468289889:ℚ)/2212000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((7531629:ℚ)/15625000),((-555413897580551781371815146861093014166977332466927539:ℚ)/109863281250000000000000000000000000000000000000000000000),((-45703126403503556825758601:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6852851843:ℚ)/10000000000),((876530747:ℚ)/1250000000),((65515666587:ℚ)/114400000000),((932530747:ℚ)/1406250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4471316453:ℚ)/10000000000),((-4345347327859650475318277484662736888987647548847495831:ℚ)/850678400000000000000000000000000000000000000000000000000),((-45767752875361795703345321:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((1742914577:ℚ)/2500000000),((3535821833:ℚ)/5000000000),((5548743731:ℚ)/9612500000),((3759821833:ℚ)/5720000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4094913383:ℚ)/10000000000),((-22481411486072807592378772757706237151433115181539079:ℚ)/4163421102905273437500000000000000000000000000000000000),((-2864551630498321521621441:ℚ)/23104000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((3515530421:ℚ)/5000000000),((1426208197:ℚ)/2000000000),((33559773789:ℚ)/58150000000),((505269399:ℚ)/769000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3893932093:ℚ)/10000000000),((-266419784534584322107859932185299306465988758588567347:ℚ)/49157429593750000000000000000000000000000000000000000000),((-11466382557850692199662489:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((9:ℚ)/16),((5:ℚ)/8),((3545231463:ℚ)/5000000000),((7190437943:ℚ)/10000000000),((33827083167:ℚ)/58625000000),((7638437943:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((184129301:ℚ)/500000000),((-34943687947665419380322237531240141826919414921643769:ℚ)/6424990844726562500000000000000000000000000000000000000),((-34423759553555775182999603:ℚ)/277248000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7149864571:ℚ)/10000000000),((7249834547:ℚ)/10000000000),((22729593713:ℚ)/39400000000),((7697834547:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((34589717:ℚ)/100000000),((-521484815748013606991916859725128174225288221867513439:ℚ)/95567162500000000000000000000000000000000000000000000000),((-45931273611551736898389689:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((7209265787:ℚ)/10000000000),((7309230807:ℚ)/10000000000),((68723392083:ℚ)/119150000000),((7757230807:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((32205303:ℚ)/100000000),((-57869874602244320490442731664943129003041771156870947141:ℚ)/10572121786718750000000000000000000000000000000000000000000),((-45964312854924466441494201:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1453733317:ℚ)/2000000000),((736862673:ℚ)/1000000000),((13851599853:ℚ)/24020000000),((781662673:ℚ)/1191500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((592736117:ℚ)/2000000000),((-29720093323614663781424894218373792792882660921970731:ℚ)/5413511253125000000000000000000000000000000000000000000),((-1839898552209996209594681:ℚ)/14786560000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((293122679:ℚ)/400000000),((1857005581:ℚ)/2500000000),((930568037:ℚ)/1614000000),((1969005581:ℚ)/3002500000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2683136107:ℚ)/10000000000),((-48222207547959830315651205709709496354213332519233:ℚ)/8759299050000000000000000000000000000000000000000000),((-73649162345238539656689:ℚ)/591462400000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((1477493393:ℚ)/2000000000),((3743708799:ℚ)/5000000000),((14065440537:ℚ)/24400000000),((3967708799:ℚ)/6052500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((59262333:ℚ)/250000000),((-501143510864120123791019918674908195313958707752595399:ℚ)/90792400000000000000000000000000000000000000000000000000),((-1842564033547713603363521:ℚ)/14786560000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((7446866567:ℚ)/10000000000),((1901551803:ℚ)/2500000000),((23620599701:ℚ)/41300000000),((2013551803:ℚ)/3050000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2010829009:ℚ)/10000000000),((-584190843466701835632580313585914141637805963060458443:ℚ)/110070307812500000000000000000000000000000000000000000000),((-46097586928521048328841681:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7565664637:ℚ)/10000000000),((7724995629:ℚ)/10000000000),((71930981733:ℚ)/125800000000),((8172995629:ℚ)/12390000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((950917117:ℚ)/10000000000),((-64840183298408688837483288707754467872328276639920139:ℚ)/12151278759765625000000000000000000000000000000000000000),((-46164894267185538669253801:ℚ)/369664000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((3842230627:ℚ)/5000000000),((3981284541:ℚ)/5000000000),((12166691881:ℚ)/21600000000),((4205284541:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-142265377874807059425280055630469803547657109741541:ℚ)/28800000000000000000000000000000000000000000000000000),((-15991839:ℚ)/128000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((3961025193:ℚ)/5000000000),((9863031059:ℚ)/10000000000),((37569226737:ℚ)/80000000000),((3437010353:ℚ)/4320000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-16542872864040045883250721238650557:ℚ)/24000000000000000000000000000000000000),((-15991839:ℚ)/128000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((4911305481:ℚ)/5000000000),((6831786649:ℚ)/5000000000),((15373916443:ℚ)/36800000000),((7055786649:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1801938931054720148234931:ℚ)/677120000000000000000000000),((-15991839:ℚ)/128000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC26
#check @N11Formalization.C450EighthGroupedC26.bound
#print axioms N11Formalization.C450EighthGroupedC26.valid0
#print axioms N11Formalization.C450EighthGroupedC26.valid1
#print axioms N11Formalization.C450EighthGroupedC26.valid2
#print axioms N11Formalization.C450EighthGroupedC26.valid3
#print axioms N11Formalization.C450EighthGroupedC26.valid4
#print axioms N11Formalization.C450EighthGroupedC26.valid5
#print axioms N11Formalization.C450EighthGroupedC26.valid6
#print axioms N11Formalization.C450EighthGroupedC26.valid7
#print axioms N11Formalization.C450EighthGroupedC26.valid8
#print axioms N11Formalization.C450EighthGroupedC26.valid9
#print axioms N11Formalization.C450EighthGroupedC26.valid10
#print axioms N11Formalization.C450EighthGroupedC26.valid11
#print axioms N11Formalization.C450EighthGroupedC26.valid12
#print axioms N11Formalization.C450EighthGroupedC26.valid13
#print axioms N11Formalization.C450EighthGroupedC26.valid14
#print axioms N11Formalization.C450EighthGroupedC26.valid15
#print axioms N11Formalization.C450EighthGroupedC26.valid16
#print axioms N11Formalization.C450EighthGroupedC26.bound
#print axioms N11Formalization.C450EighthGroupedC26.endpoint_checks
