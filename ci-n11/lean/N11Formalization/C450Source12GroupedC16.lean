import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((3092183693:ℚ)/5000000000),((6688075431:ℚ)/10000000000),((-288075431:ℚ)/99200000000),((11:ℚ)/155),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3101255349:ℚ)/5000000000),((1436760817161983023:ℚ)/47665600000000000000),((-379167790048006662566692429:ℚ)/8871936000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6660482337:ℚ)/10000000000),((6807058047:ℚ)/10000000000),((-407058047:ℚ)/106800000000),((88:ℚ)/1335),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((502504157:ℚ)/1000000000),((4527515775918989673924322941881:ℚ)/154900415039062500000000000000000),((-22222625748190404505809679:ℚ)/466944000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((1355897327:ℚ)/2000000000),((3463020331:ℚ)/5000000000),((-263020331:ℚ)/54350000000),((352:ℚ)/5435),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((293101511:ℚ)/625000000),((14247984419202461542970705451337:ℚ)/489946557235717773437500000000000),((-36078430976110039311893543:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((862310271:ℚ)/1250000000),((704502327:ℚ)/1000000000),((-64502327:ℚ)/11060000000),((176:ℚ)/2765),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2165190971:ℚ)/5000000000),((8536245273181761100195725940349:ℚ)/294908581542968750000000000000000),((-4436504650685187972631981:ℚ)/88719360000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((3508734691:ℚ)/5000000000),((1776128359:ℚ)/2500000000),((-58709453:ℚ)/9375000000),((352:ℚ)/5625),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((985193247:ℚ)/2500000000),((27804833514364437432259645784293:ℚ)/965595245361328125000000000000000),((-9466534193559075502686703:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((7076960001:ℚ)/10000000000),((1791000421:ℚ)/2500000000),((-191000421:ℚ)/28362500000),((704:ℚ)/11345),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3731628539:ℚ)/10000000000),((20490085754118396039598211229369:ℚ)/712990179992675781250000000000000),((-9578060320457990055493383:ℚ)/184832000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((3568224347:ℚ)/5000000000),((7223488061:ℚ)/10000000000),((-74862551:ℚ)/10400000000),((4:ℚ)/65),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3510667069:ℚ)/10000000000),((96157811883825223031190739:ℚ)/3352355957031250000000000000),((-155033225795467330692945623:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((7195935509:ℚ)/10000000000),((3641486307:ℚ)/5000000000),((-441486307:ℚ)/57675000000),((704:ℚ)/11535),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((818873363:ℚ)/2500000000),((596028785813770257792293018011:ℚ)/20817105514526367187500000000000),((-117612997912890719060411461:ℚ)/2217984000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/16),(0:ℚ),((7255420493:ℚ)/10000000000),((3671227693:ℚ)/5000000000),((-471227693:ℚ)/58150000000),((352:ℚ)/5815),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((94462111:ℚ)/312500000),((34302507270563689027889055673151:ℚ)/1200132558441162109375000000000000),((-39650320202990451071322487:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7314903689:ℚ)/10000000000),((3700968211:ℚ)/5000000000),((-500968211:ℚ)/58625000000),((704:ℚ)/11725),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2747711077:ℚ)/10000000000),((561476303877455037876230921982941:ℚ)/19676534461975097656250000000000000),((-40096269469443840957356023:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((7374385141:ℚ)/10000000000),((7520893447:ℚ)/10000000000),((-373631149:ℚ)/39400000000),((176:ℚ)/2955),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1221356167:ℚ)/5000000000),((23951814646757981687095648642469:ℚ)/839945764160156250000000000000000),((-162156184818990827857566767:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((7493342981:ℚ)/10000000000),((7639844007:ℚ)/10000000000),((-1239844007:ℚ)/120100000000),((352:ℚ)/6005),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1677305363:ℚ)/10000000000),((300633963487130548268440634884493:ℚ)/10573264166259765625000000000000000),((-54516898031647857:ℚ)/972800000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((761229433:ℚ)/1000000000),((8115587307:ℚ)/10000000000),((-1715587307:ℚ)/122000000000),((88:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((40462461808740106049576939089:ℚ)/1419448852539062500000000000000),((-58501369:ℚ)/1024000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((8088040551:ℚ)/10000000000),((5008926581:ℚ)/5000000000),((-602975527:ℚ)/21600000000),((22:ℚ)/405),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((62347627993879861809838998733:ℚ)/2162438964843750000000000000000),((-58501369:ℚ)/1024000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((2497578827:ℚ)/2500000000),((691025557:ℚ)/500000000),((-371025557:ℚ)/8000000000),((11:ℚ)/250),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5057767224949:ℚ)/160000000000000),((-58501369:ℚ)/1024000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC16
#check @N11Formalization.C450Source12GroupedC16.bound
#print axioms N11Formalization.C450Source12GroupedC16.valid0
#print axioms N11Formalization.C450Source12GroupedC16.valid1
#print axioms N11Formalization.C450Source12GroupedC16.valid2
#print axioms N11Formalization.C450Source12GroupedC16.valid3
#print axioms N11Formalization.C450Source12GroupedC16.valid4
#print axioms N11Formalization.C450Source12GroupedC16.valid5
#print axioms N11Formalization.C450Source12GroupedC16.valid6
#print axioms N11Formalization.C450Source12GroupedC16.valid7
#print axioms N11Formalization.C450Source12GroupedC16.valid8
#print axioms N11Formalization.C450Source12GroupedC16.valid9
#print axioms N11Formalization.C450Source12GroupedC16.valid10
#print axioms N11Formalization.C450Source12GroupedC16.valid11
#print axioms N11Formalization.C450Source12GroupedC16.valid12
#print axioms N11Formalization.C450Source12GroupedC16.valid13
#print axioms N11Formalization.C450Source12GroupedC16.valid14
#print axioms N11Formalization.C450Source12GroupedC16.bound
#print axioms N11Formalization.C450Source12GroupedC16.endpoint_checks
