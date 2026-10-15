import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5968279241:ℚ)/10000000000),((3245150973:ℚ)/5000000000),((16059318229:ℚ)/35600000000),((3685150973:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3338079739:ℚ)/5000000000),((93736182686267723107513:ℚ)/31684000000000000000000000),((-511860582890951313681124967:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6444114717:ℚ)/10000000000),((1682033903:ℚ)/2500000000),((51508803019:ℚ)/110600000000),((634011301:ℚ)/1112500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1117532447:ℚ)/2000000000),((211682530842223066252692635339713:ℚ)/436870000000000000000000000000000000),((-1558610319809885144143478669:ℚ)/8871936000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((3340994647:ℚ)/5000000000),((855880497:ℚ)/1250000000),((8862320843:ℚ)/18750000000),((965880497:ℚ)/1728125000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2482983373:ℚ)/5000000000),((-17780592897591389420215200287449:ℚ)/29296875000000000000000000000000000),((-130846672834466233805085863:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((425057317:ℚ)/625000000),((6965947069:ℚ)/10000000000),((3375401219:ℚ)/7150000000),((7845947069:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4626844601:ℚ)/10000000000),((-9216147521759073519486529784963:ℚ)/12780625000000000000000000000000000),((-2052010255951813317925023:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((6919838931:ℚ)/10000000000),((87817459:ℚ)/125000000),((54838872517:ℚ)/115350000000),((7601343:ℚ)/13750000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4262923189:ℚ)/10000000000),((-673821496031213745509645980950613:ℚ)/554400937500000000000000000000000000),((-4381533652691147098067621:ℚ)/24576000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6979297733:ℚ)/10000000000),((141696903:ℚ)/200000000),((55255084131:ℚ)/116300000000),((159296903:ℚ)/288375000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((813918517:ℚ)/2000000000),((-851222303855542361566067594694999:ℚ)/676284500000000000000000000000000000),((-528210259134902113416150623:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/16),((1:ℚ)/2),((1759688791:ℚ)/2500000000),((7144292387:ℚ)/10000000000),((13917821537:ℚ)/29312500000),((8024292387:ℚ)/14537500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1933588137:ℚ)/5000000000),((-42508987452672663864912089509:ℚ)/32714843750000000000000000000000),((-33073529239975137643904167:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1419642251:ℚ)/2000000000),((3601869231:ℚ)/5000000000),((11217495757:ℚ)/23640000000),((4041869231:ℚ)/7328125000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3654160683:ℚ)/10000000000),((-31146193864163855345984153790329:ℚ)/23285400000000000000000000000000000),((-21205727044908259387969407:ℚ)/118292480000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((7157666041:ℚ)/10000000000),((7263183401:ℚ)/10000000000),((56503662287:ℚ)/119150000000),((2714394467:ℚ)/4925000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((857141633:ℚ)/2500000000),((-4874287837585660649460527034492301:ℚ)/3549180625000000000000000000000000000),((-531110384518497325467708167:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((112767493:ℚ)/156250000),((7322627231:ℚ)/10000000000),((889372451:ℚ)/1876562500),((8202627231:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((637543977:ℚ)/2000000000),((-619233579446269876296337873663:ℚ)/440185852050781250000000000000000),((-129901878291279259814943:ℚ)/722000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((3638285909:ℚ)/5000000000),((369103499:ℚ)/500000000),((28668001363:ℚ)/60525000000),((413103499:ℚ)/750625000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((292785427:ℚ)/1000000000),((-438934204133879385312357337100447:ℚ)/305272968750000000000000000000000000),((-133261575866403024092146367:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((7336022869:ℚ)/10000000000),((7441511671:ℚ)/10000000000),((57752160083:ℚ)/122000000000),((8321511671:ℚ)/15131250000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((660840277:ℚ)/2500000000),((-5457494626070178796900952809380421:ℚ)/3721000000000000000000000000000000000),((-534015014928304977558542527:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3697736367:ℚ)/5000000000),((7560391981:ℚ)/10000000000),((29084154569:ℚ)/61950000000),((8440391981:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1162606143:ℚ)/5000000000),((-25835299117069889447578250081261:ℚ)/22844062500000000000000000000000000),((-401238171232586090743539269:ℚ)/2217984000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7514369013:ℚ)/10000000000),((1919817087:ℚ)/2500000000),((59000583091:ℚ)/125800000000),((2139817087:ℚ)/3871875000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((37564041:ℚ)/250000000),((-146436278147747351393701048729073:ℚ)/123637812500000000000000000000000000),((-1610772487359222460696660349:ℚ)/8871936000000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((1526652173:ℚ)/2000000000),((7917009951:ℚ)/10000000000),((11966565211:ℚ)/25920000000),((8797009951:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-30768914811387610319368398420359:ℚ)/55987200000000000000000000000000000),((-186399801:ℚ)/1024000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((787103207:ℚ)/1000000000),((9818529159:ℚ)/10000000000),((6149722449:ℚ)/16000000000),((10698529159:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((105423631067397572948886323860803:ℚ)/16000000000000000000000000000000000),((-186399801:ℚ)/1024000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((122159217:ℚ)/125000000),((6810155853:ℚ)/5000000000),((40657153:ℚ)/120000000),((7250155853:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1626585204141323179:ℚ)/120000000000000000000),((-186399801:ℚ)/1024000000)⟩
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
end N11Formalization.C450Source12GroupedC24
#check @N11Formalization.C450Source12GroupedC24.bound
#print axioms N11Formalization.C450Source12GroupedC24.valid0
#print axioms N11Formalization.C450Source12GroupedC24.valid1
#print axioms N11Formalization.C450Source12GroupedC24.valid2
#print axioms N11Formalization.C450Source12GroupedC24.valid3
#print axioms N11Formalization.C450Source12GroupedC24.valid4
#print axioms N11Formalization.C450Source12GroupedC24.valid5
#print axioms N11Formalization.C450Source12GroupedC24.valid6
#print axioms N11Formalization.C450Source12GroupedC24.valid7
#print axioms N11Formalization.C450Source12GroupedC24.valid8
#print axioms N11Formalization.C450Source12GroupedC24.valid9
#print axioms N11Formalization.C450Source12GroupedC24.valid10
#print axioms N11Formalization.C450Source12GroupedC24.valid11
#print axioms N11Formalization.C450Source12GroupedC24.valid12
#print axioms N11Formalization.C450Source12GroupedC24.valid13
#print axioms N11Formalization.C450Source12GroupedC24.valid14
#print axioms N11Formalization.C450Source12GroupedC24.valid15
#print axioms N11Formalization.C450Source12GroupedC24.valid16
#print axioms N11Formalization.C450Source12GroupedC24.bound
#print axioms N11Formalization.C450Source12GroupedC24.endpoint_checks
