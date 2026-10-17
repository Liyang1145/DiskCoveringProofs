import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5923623531:ℚ)/10000000000),((806378791:ℚ)/1250000000),((16381788239:ℚ)/35600000000),((936378791:ℚ)/1550000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((677050197:ℚ)/1000000000),((181242818660476597972963:ℚ)/39605000000000000000000000),((-2501716027467672457911:ℚ)/11875000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6399791661:ℚ)/10000000000),((3344505627:ℚ)/5000000000),((52478541627:ℚ)/110600000000),((3864505627:ℚ)/6675000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1424180367:ℚ)/2500000000),((13947024850312947231251093056089887:ℚ)/11467837500000000000000000000000000000),((-772816062783390536079781:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((3318907661:ℚ)/5000000000),((3403994749:ℚ)/5000000000),((27072353627:ℚ)/56250000000),((3923994749:ℚ)/6912500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((203464927:ℚ)/400000000),((-86339532213929389604739560664209:ℚ)/329589843750000000000000000000000000),((-778959445635146370096789:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((1689203461:ℚ)/2500000000),((346348007:ℚ)/500000000),((13744424227:ℚ)/28600000000),((132782669:ℚ)/234375000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((237760363:ℚ)/500000000),((-103722717383630630160087705754697:ℚ)/255612500000000000000000000000000000),((-7819869466698217997661:ℚ)/36100000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6875804087:ℚ)/10000000000),((220185111:ℚ)/312500000),((55810628609:ℚ)/116300000000),((252685111:ℚ)/446875000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4400953073:ℚ)/10000000000),((-3385976676777957981726680059041503:ℚ)/6340167187500000000000000000000000000),((-6132912056276334432413:ℚ)/28203125000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/16),((1:ℚ)/2),((874348307:ℚ)/1250000000),((3552701329:ℚ)/5000000000),((7080438149:ℚ)/14656250000),((4072701329:ℚ)/7268750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((200889657:ℚ)/500000000),((-1895174728665785345435784797197979:ℚ)/1611042480468750000000000000000000000),((-788081617914048064723149:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7054274809:ℚ)/10000000000),((3582440043:ℚ)/5000000000),((57059923663:ℚ)/118200000000),((4102440043:ℚ)/7328125000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((762533357:ℚ)/2000000000),((-889610314907949103045740996056179:ℚ)/727668750000000000000000000000000000),((-789593409160456093369861:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((3556880667:ℚ)/5000000000),((7224355877:ℚ)/10000000000),((28738164669:ℚ)/59575000000),((8264355877:ℚ)/14775000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3596466877:ℚ)/10000000000),((-8421203285782983864462671454693869:ℚ)/6654713671875000000000000000000000000),((-3164419122441253723343781:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((1793311519:ℚ)/2500000000),((7283830069:ℚ)/10000000000),((14473180633:ℚ)/30025000000),((8323830069:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3367056597:ℚ)/10000000000),((-91921486814464755602436977516561:ℚ)/70429736328125000000000000000000000),((-3170462933770789937055429:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((7232729077:ℚ)/10000000000),((7402773807:ℚ)/10000000000),((58309103539:ℚ)/122000000000),((8442773807:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1560760009:ℚ)/5000000000),((-3876937958572436341565733734651799:ℚ)/4651250000000000000000000000000000000),((-3176320035309747087344461:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((367584501:ℚ)/500000000),((7521711589:ℚ)/10000000000),((985697169:ℚ)/2065000000),((8561711589:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((512654631:ℚ)/2000000000),((-151126124235769190538865998519:ℚ)/166571289062500000000000000000000),((-3188396349096139553061669:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7470644477:ℚ)/10000000000),((3820321843:ℚ)/5000000000),((59974511339:ℚ)/125800000000),((73564777:ℚ)/131250000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1847645347:ℚ)/10000000000),((-8809641894568475258689153148659:ℚ)/9091015625000000000000000000000000),((-842262298330011:ℚ)/3800000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((3794796371:ℚ)/5000000000),((7878491827:ℚ)/10000000000),((30403574597:ℚ)/64800000000),((8918491827:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((523390621:ℚ)/10000000000),((-37114236340302507406596648659381:ℚ)/437400000000000000000000000000000000),((-422769245196453:ℚ)/1900000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((782747179:ℚ)/1000000000),((489034033:ℚ)/500000000),((6247230253:ℚ)/16000000000),((541034033:ℚ)/810000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((583930426604970941111794274175251:ℚ)/60000000000000000000000000000000000),((-3561369:ℚ)/16000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((9729854851:ℚ)/10000000000),((13583248351:ℚ)/10000000000),((75788983957:ℚ)/220800000000),((14623248351:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((9896473669718907401098649:ℚ)/507840000000000000000000000),((-3561369:ℚ)/16000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC24
#check @N11Formalization.C450Source14GroupedC24.bound
#print axioms N11Formalization.C450Source14GroupedC24.valid0
#print axioms N11Formalization.C450Source14GroupedC24.valid1
#print axioms N11Formalization.C450Source14GroupedC24.valid2
#print axioms N11Formalization.C450Source14GroupedC24.valid3
#print axioms N11Formalization.C450Source14GroupedC24.valid4
#print axioms N11Formalization.C450Source14GroupedC24.valid5
#print axioms N11Formalization.C450Source14GroupedC24.valid6
#print axioms N11Formalization.C450Source14GroupedC24.valid7
#print axioms N11Formalization.C450Source14GroupedC24.valid8
#print axioms N11Formalization.C450Source14GroupedC24.valid9
#print axioms N11Formalization.C450Source14GroupedC24.valid10
#print axioms N11Formalization.C450Source14GroupedC24.valid11
#print axioms N11Formalization.C450Source14GroupedC24.valid12
#print axioms N11Formalization.C450Source14GroupedC24.valid13
#print axioms N11Formalization.C450Source14GroupedC24.valid14
#print axioms N11Formalization.C450Source14GroupedC24.bound
#print axioms N11Formalization.C450Source14GroupedC24.endpoint_checks
