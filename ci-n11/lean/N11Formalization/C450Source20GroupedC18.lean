import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((3029488177:ℚ)/5000000000),((411950469:ℚ)/625000000),((8789488177:ℚ)/53400000000),((791950469:ℚ)/3100000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1296194979:ℚ)/2000000000),((18443094522452233149973573170823065983:ℚ)/265471324875000000000000000000000000000),((-4696592747261772641105783:ℚ)/21660000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6537273363:ℚ)/10000000000),((683004773:ℚ)/1000000000),((18057273363:ℚ)/110600000000),((1291004773:ℚ)/5340000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5351982279:ℚ)/10000000000),((28705629882969964236971417374693085661783393168662923962311:ℚ)/436561376465025000000000000000000000000000000000000000000000),((-4267867057077424197318229:ℚ)/18483200000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6776250339:ℚ)/10000000000),((1389886723:ℚ)/2000000000),((6098750113:ℚ)/37500000000),((2605886723:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((469903723:ℚ)/1000000000),((349378456921577260907702796411086152040789773369008029:ℚ)/5435754975000000000000000000000000000000000000000000000),((-17590816619664225031775429:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((1723925269:ℚ)/2500000000),((3534399107:ℚ)/5000000000),((4603925269:ℚ)/28600000000),((2191466369:ℚ)/9375000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4339094101:ℚ)/10000000000),((3364094731737053027317359241744673024688119635045636654361:ℚ)/52654552459716796875000000000000000000000000000000000000000),((-111504555851487740341150149:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((7015128337:ℚ)/10000000000),((7188142581:ℚ)/10000000000),((18535128337:ℚ)/116300000000),((13268142581:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3948787849:ℚ)/10000000000),((37698952430530789672840296879051785624309175409639455680963743:ℚ)/593278760667450000000000000000000000000000000000000000000000000),((-1356770068155187850270335583:ℚ)/5544960000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((3567266643:ℚ)/5000000000),((73074677:ℚ)/100000000),((3109088881:ℚ)/19700000000),((133874677:ℚ)/581500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3517988267:ℚ)/10000000000),((1130922078219587985581147601872125544082818970501331631:ℚ)/17885162672848535156250000000000000000000000000000000000),((-45848587897830342711029:ℚ)/184832000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((725391701:ℚ)/1000000000),((1485354899:ℚ)/2000000000),((1877391701:ℚ)/12010000000),((900451633:ℚ)/3940000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3029425737:ℚ)/10000000000),((52068570643309045917907247265581276054001269514083402099339:ℚ)/827077024542975000000000000000000000000000000000000000000000),((-18588234135461256636142501:ℚ)/73932800000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7373280527:ℚ)/10000000000),((1886515957:ℚ)/2500000000),((18893280527:ℚ)/122000000000),((3406515957:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2448714799:ℚ)/10000000000),((2467169283259892292240020453723714662350017243402814745557:ℚ)/39343115962652587890625000000000000000000000000000000000000),((-29432291871340277686698549:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7492624791:ℚ)/10000000000),((8023062037:ℚ)/10000000000),((6337541597:ℚ)/43200000000),((14103062037:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((420739099:ℚ)/2500000000),((8255608919949433513933177516083427328429107378787043562213:ℚ)/129272772656250000000000000000000000000000000000000000000000),((-62816053167457673:ℚ)/243200000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((3984913203:ℚ)/5000000000),((2482286959:ℚ)/2500000000),((9744913203:ℚ)/80000000000),((444698551:ℚ)/1800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((230143260359824392739841925868075617621069300301853:ℚ)/3417187500000000000000000000000000000000000000000000),((-6695927:ℚ)/25600000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((9876530723:ℚ)/10000000000),((858517379:ℚ)/625000000),((21396530723:ℚ)/220800000000),((1238517379:ℚ)/5000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5876030518216036646990422494670272607:ℚ)/74390625000000000000000000000000000000),((-6695927:ℚ)/25600000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC18
#check @N11Formalization.C450Source20GroupedC18.bound
#print axioms N11Formalization.C450Source20GroupedC18.valid0
#print axioms N11Formalization.C450Source20GroupedC18.valid1
#print axioms N11Formalization.C450Source20GroupedC18.valid2
#print axioms N11Formalization.C450Source20GroupedC18.valid3
#print axioms N11Formalization.C450Source20GroupedC18.valid4
#print axioms N11Formalization.C450Source20GroupedC18.valid5
#print axioms N11Formalization.C450Source20GroupedC18.valid6
#print axioms N11Formalization.C450Source20GroupedC18.valid7
#print axioms N11Formalization.C450Source20GroupedC18.valid8
#print axioms N11Formalization.C450Source20GroupedC18.valid9
#print axioms N11Formalization.C450Source20GroupedC18.valid10
#print axioms N11Formalization.C450Source20GroupedC18.bound
#print axioms N11Formalization.C450Source20GroupedC18.endpoint_checks
