import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((11:ℚ)/16),((3:ℚ)/4),((2607755277:ℚ)/5000000000),((222129869:ℚ)/400000000),((38285308047:ℚ)/51500000000),((864789607:ℚ)/992000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8144735789:ℚ)/10000000000),((-8551131996149892192201903639062622068699477:ℚ)/25284217520000000000000000000000000000000000),((-5684141571261992060365791:ℚ)/11829248000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5455037683:ℚ)/10000000000),((724109191:ℚ)/1250000000),((79205414513:ℚ)/106800000000),((2792327573:ℚ)/3218750000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((770204757:ℚ)/1000000000),((-335939217086292412503792811928260434558302948656742905313:ℚ)/990542285957336425781250000000000000000000000000000000000),((-54678197476956495082258711:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((142360471:ℚ)/250000000),((5912630451:ℚ)/10000000000),((2045965181:ℚ)/2717500000),((22697891353:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7238438031:ℚ)/10000000000),((-3287046794958445603039672442346537129600498728763269698289023:ℚ)/9370907059061250000000000000000000000000000000000000000000000),((-10416396878990952362325953693:ℚ)/22179840000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((363378721:ℚ)/625000000),((188511011:ℚ)/312500000),((5197165931:ℚ)/6912500000),((720533033:ℚ)/849218750),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((699742833:ℚ)/1000000000),((-4399375060283225584175831239712753012757612525169616957:ℚ)/12541579245677813887596130371093750000000000000000000000),((-3363678025636970257567551:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((5933669297:ℚ)/10000000000),((1230408207:ℚ)/2000000000),((84470362267:ℚ)/112500000000),((4683224621:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1687343933:ℚ)/2500000000),((-372413115894182166514761662889643487364993305405071:ℚ)/1061670893554687500000000000000000000000000000000000),((-409947195736031958395493557:ℚ)/887193600000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6053249711:ℚ)/10000000000),((776484181:ℚ)/1250000000),((85785746821:ℚ)/113450000000),((2949452543:ℚ)/3515625000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((649344669:ℚ)/1000000000),((-62192091644845853596603640607806628839245394950866139571:ℚ)/174769906746223568916320800781250000000000000000000000000),((-53155729125887551513037391:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6113029381:ℚ)/10000000000),((3135849089:ℚ)/5000000000),((86443323191:ℚ)/114400000000),((11887547267:ℚ)/14181250000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6362224403:ℚ)/10000000000),((-207488451903119595673349561373191632451682596414359903876373:ℚ)/583197447626809082031250000000000000000000000000000000000000),((-846898317738801223805329351:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6172802261:ℚ)/10000000000),((3165757709:ℚ)/5000000000),((87100824871:ℚ)/115350000000),((11977273127:ℚ)/14300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1245728729:ℚ)/2000000000),((-90103063189871442362852919893238164221343692057209056473:ℚ)/253309859725634765625000000000000000000000000000000000000),((-843276612326041252178498911:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1558142131:ℚ)/2500000000),((6391325353:ℚ)/10000000000),((21939563441:ℚ)/29075000000),((24133976059:ℚ)/28837500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3046272999:ℚ)/5000000000),((-4806369789825797925676873138895526460838088193919215560933109:ℚ)/13515154362565158691406250000000000000000000000000000000000000),((-3358506197047082766281585079:ℚ)/7393280000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((6292328331:ℚ)/10000000000),((1612782041:ℚ)/2500000000),((12630801663:ℚ)/16750000000),((6078346123:ℚ)/7268750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2976877779:ℚ)/5000000000),((-2298606993614851297438094718636234620180277929823605247053:ℚ)/6464874065810852050781250000000000000000000000000000000000),((-208987031980305447496205911:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1588020461:ℚ)/2500000000),((813865503:ℚ)/1250000000),((22268225071:ℚ)/29550000000),((3061596509:ℚ)/3664062500),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((726509509:ℚ)/1250000000),((-5426160107017952247531633205405274170258039877420096009:ℚ)/15264391509890556335449218750000000000000000000000000000),((-156045252717688012643676437:ℚ)/346560000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3205914607:ℚ)/5000000000),((1657623891:ℚ)/2500000000),((44865060677:ℚ)/60050000000),((6212871673:ℚ)/7387500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5667287503:ℚ)/10000000000),((-191182165990372077773072123572543098827147724561732481406543:ℚ)/545192374576668090820312500000000000000000000000000000000000),((-618557031752939774300138333:ℚ)/1386240000000000000000000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((6531306121:ℚ)/10000000000),((6750041257:ℚ)/10000000000),((91044367331:ℚ)/122000000000),((25210123771:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5367357363:ℚ)/10000000000),((-132429402167645770032662596910175846246597012596150696262869:ℚ)/377693913241464843750000000000000000000000000000000000000000),((-3268522515051420785556065719:ℚ)/7393280000000000000000000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((831345023:ℚ)/1250000000),((6989059847:ℚ)/10000000000),((11544795253:ℚ)/15725000000),((25927179541:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1262884657:ℚ)/2500000000),((-3594642915060962441060365344372367869433442802822700680428411:ℚ)/10523787869648437500000000000000000000000000000000000000000000),((-3206264515842103924784377879:ℚ)/7393280000000000000000000000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((53825031:ℚ)/78125000),((3613994289:ℚ)/5000000000),((247358447:ℚ)/337500000),((21179623:ℚ)/25000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((544767133:ℚ)/1250000000),((-1622418232293332358811017510418406473027935489193:ℚ)/4746093750000000000000000000000000000000000000000),((-2356643461502443917124588853:ℚ)/5544960000000000000000000000)⟩
theorem valid14 : Valid source32 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7128368319:ℚ)/10000000000),((571059931:ℚ)/625000000),((97612051509:ℚ)/160000000000),((2023179793:ℚ)/2025000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3541453923:ℚ)/10000000000),((-13884015934786662214643436848301447645056039319736141:ℚ)/62278242187500000000000000000000000000000000000000000),((-210441141:ℚ)/512000000)⟩
theorem valid15 : Valid source32 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((9036308241:ℚ)/10000000000),((12947458933:ℚ)/10000000000),((39533130217:ℚ)/73600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-479294951655159828961536313:ℚ)/2708480000000000000000000000),((-210441141:ℚ)/512000000)⟩
theorem valid16 : Valid source32 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source32 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source32 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source32 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC28
#check @N11Formalization.C450Source32GroupedC28.bound
#print axioms N11Formalization.C450Source32GroupedC28.valid0
#print axioms N11Formalization.C450Source32GroupedC28.valid1
#print axioms N11Formalization.C450Source32GroupedC28.valid2
#print axioms N11Formalization.C450Source32GroupedC28.valid3
#print axioms N11Formalization.C450Source32GroupedC28.valid4
#print axioms N11Formalization.C450Source32GroupedC28.valid5
#print axioms N11Formalization.C450Source32GroupedC28.valid6
#print axioms N11Formalization.C450Source32GroupedC28.valid7
#print axioms N11Formalization.C450Source32GroupedC28.valid8
#print axioms N11Formalization.C450Source32GroupedC28.valid9
#print axioms N11Formalization.C450Source32GroupedC28.valid10
#print axioms N11Formalization.C450Source32GroupedC28.valid11
#print axioms N11Formalization.C450Source32GroupedC28.valid12
#print axioms N11Formalization.C450Source32GroupedC28.valid13
#print axioms N11Formalization.C450Source32GroupedC28.valid14
#print axioms N11Formalization.C450Source32GroupedC28.valid15
#print axioms N11Formalization.C450Source32GroupedC28.valid16
#print axioms N11Formalization.C450Source32GroupedC28.bound
#print axioms N11Formalization.C450Source32GroupedC28.endpoint_checks
