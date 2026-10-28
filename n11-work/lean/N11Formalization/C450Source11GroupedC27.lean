import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((369886989:ℚ)/625000000),((402755103:ℚ)/625000000),((135295663:ℚ)/222500000),((4830306133:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((423868859:ℚ)/625000000),((-40834105632450378729238883381:ℚ)/2753785156250000000000000000000),((-15966133968328771193631641:ℚ)/86640000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3196838389:ℚ)/5000000000),((6681785163:ℚ)/10000000000),((3484838389:ℚ)/5530000000),((79899636793:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1142324349:ℚ)/2000000000),((-57932731390677308768692859872386338520178603919457343:ℚ)/3170857068750000000000000000000000000000000000000000000),((-341471856725586703809654947:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((6631394227:ℚ)/10000000000),((3400315879:ℚ)/5000000000),((7207394227:ℚ)/11250000000),((40603474669:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5103944631:ℚ)/10000000000),((-58891006798732008485910482734062828527356496916028841:ℚ)/2966308593750000000000000000000000000000000000000000000),((-1367659603503597183396190003:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((1350049487:ℚ)/2000000000),((6919475141:ℚ)/10000000000),((112711499:ℚ)/176000000),((82514226551:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((298377853:ℚ)/625000000),((-61718720702049444152695710664300348166032096409:ℚ)/3097600000000000000000000000000000000000000000000),((-54742329564777023882707483:ℚ)/295731200000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((6869097211:ℚ)/10000000000),((6978895677:ℚ)/10000000000),((7445097211:ℚ)/11535000000),((83167852447:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4421622057:ℚ)/10000000000),((-148670564932313186607119100768849794824735677452022337:ℚ)/7194391665820312500000000000000000000000000000000000000),((-1369465240456828052262537347:ℚ)/7393280000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((1385704173:ℚ)/2000000000),((7038315469:ℚ)/10000000000),((1500904173:ℚ)/2326000000),((27940490053:ℚ)/38450000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((529401483:ℚ)/1250000000),((-65084464542513746905818303190376297636375393386493:ℚ)/3146075494000000000000000000000000000000000000000000),((-164390625414258486394024409:ℚ)/887193600000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((6987943723:ℚ)/10000000000),((3548867267:ℚ)/5000000000),((1080563389:ℚ)/1675000000),((42237539937:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1010188721:ℚ)/2500000000),((-456184051237852304813112310948690191520658550524647:ℚ)/22028540039062500000000000000000000000000000000000000),((-1370380608088724964392242403:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1409473161:ℚ)/2000000000),((715715289:ℚ)/1000000000),((508224387:ℚ)/788000000),((8512868179:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((767404819:ℚ)/2000000000),((-15847802268303477215880167397678345673556296103563:ℚ)/764537300000000000000000000000000000000000000000000),((-164500971532523248560773441:ℚ)/887193600000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((7106787129:ℚ)/10000000000),((3608285277:ℚ)/5000000000),((7682787129:ℚ)/11915000000),((42891138047:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3622451149:ℚ)/10000000000),((-219340663649026824923698188850994469875536142356008441:ℚ)/10572121786718750000000000000000000000000000000000000000),((-4113913027672267593540710561:ℚ)/22179840000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7166207713:ℚ)/10000000000),((3637993771:ℚ)/5000000000),((7742207713:ℚ)/12010000000),((43217931481:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((848744173:ℚ)/2500000000),((-14050900084330865713710155500106018121697155735564353:ℚ)/676688906640625000000000000000000000000000000000000000),((-3799915090052122486668803:ℚ)/20480000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((289025103:ℚ)/400000000),((733540387:ℚ)/1000000000),((104021701:ℚ)/161400000),((8708944257:ℚ)/12010000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((393975509:ℚ)/1250000000),((-182018184021324437994206041048308432712431452063:ℚ)/8759299050000000000000000000000000000000000000000),((-6586734932905547078052689:ℚ)/35487744000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((7285046733:ℚ)/10000000000),((3697409777:ℚ)/5000000000),((7861046733:ℚ)/12200000000),((14623835849:ℚ)/20175000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((361120887:ℚ)/1250000000),((-235997963433020710733720228217507329286777351301988293:ℚ)/11349050000000000000000000000000000000000000000000000000),((-4118116899488792612271266969:ℚ)/22179840000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3672232601:ℚ)/5000000000),((7513649049:ℚ)/10000000000),((3960232601:ℚ)/6195000000),((89050139539:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((650126193:ℚ)/2500000000),((-833083841925896202630400154395067176032744144950441:ℚ)/41276365429687500000000000000000000000000000000000000),((-343294228494081711322780107:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3731650069:ℚ)/5000000000),((381623807:ℚ)/500000000),((4019650069:ℚ)/6290000000),((1505953959:ℚ)/2065000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((75981061:ℚ)/400000000),((-30708316832179042247261075654911800287385823762309:ℚ)/1518909844970703125000000000000000000000000000000000),((-343531437962478458578109027:ℚ)/1848320000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((3791066253:ℚ)/5000000000),((1574024707:ℚ)/2000000000),((1359688751:ℚ)/2160000000),((18594271777:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((68584369:ℚ)/1000000000),((-44513471818460373627295310789738221763463606199373:ℚ)/2332800000000000000000000000000000000000000000000000),((-1031312218800951182158680089:ℚ)/5544960000000000000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((7819789989:ℚ)/10000000000),((9771050473:ℚ)/10000000000),((8395789989:ℚ)/16000000000),((37960518401:ℚ)/43200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-11789920294999773105252286358775847299864014458366989:ℚ)/1600000000000000000000000000000000000000000000000000000),((-95237369:ℚ)/512000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9720780357:ℚ)/10000000000),((13572138293:ℚ)/10000000000),((3432260119:ℚ)/7360000000),((155693521223:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5281251156110111227139:ℚ)/6771200000000000000000000),((-95237369:ℚ)/512000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC27
#check @N11Formalization.C450Source11GroupedC27.bound
#print axioms N11Formalization.C450Source11GroupedC27.valid0
#print axioms N11Formalization.C450Source11GroupedC27.valid1
#print axioms N11Formalization.C450Source11GroupedC27.valid2
#print axioms N11Formalization.C450Source11GroupedC27.valid3
#print axioms N11Formalization.C450Source11GroupedC27.valid4
#print axioms N11Formalization.C450Source11GroupedC27.valid5
#print axioms N11Formalization.C450Source11GroupedC27.valid6
#print axioms N11Formalization.C450Source11GroupedC27.valid7
#print axioms N11Formalization.C450Source11GroupedC27.valid8
#print axioms N11Formalization.C450Source11GroupedC27.valid9
#print axioms N11Formalization.C450Source11GroupedC27.valid10
#print axioms N11Formalization.C450Source11GroupedC27.valid11
#print axioms N11Formalization.C450Source11GroupedC27.valid12
#print axioms N11Formalization.C450Source11GroupedC27.valid13
#print axioms N11Formalization.C450Source11GroupedC27.valid14
#print axioms N11Formalization.C450Source11GroupedC27.valid15
#print axioms N11Formalization.C450Source11GroupedC27.valid16
#print axioms N11Formalization.C450Source11GroupedC27.bound
#print axioms N11Formalization.C450Source11GroupedC27.endpoint_checks
