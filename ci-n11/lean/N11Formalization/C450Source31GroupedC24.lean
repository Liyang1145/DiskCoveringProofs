import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/16),((1:ℚ)/2),((5512282713:ℚ)/10000000000),((730616207:ℚ)/1250000000),((57145978991:ℚ)/103000000000),((1030616207:ℚ)/1550000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7593257419:ℚ)/10000000000),((-70140558586369030903860292756097816036487119407111503349:ℚ)/246916186718750000000000000000000000000000000000000000000),((-91270671009624249434459:ℚ)/225625000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5753062743:ℚ)/10000000000),((380343429:ℚ)/625000000),((58831439201:ℚ)/106800000000),((530343429:ℚ)/804687500),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7121144073:ℚ)/10000000000),((-174280569934454860087712615242961595129969272655250744913:ℚ)/619088928723335266113281250000000000000000000000000000000),((-45334313491430907293187:ℚ)/112812500000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((2996802427:ℚ)/5000000000),((3102847807:ℚ)/5000000000),((30257616989:ℚ)/54350000000),((4302847807:ℚ)/6675000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((331107519:ℚ)/500000000),((-23216696073357247920738671710843127298246866391062528101127:ℚ)/81344679332128906250000000000000000000000000000000000000000),((-1454923843136516619044109:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3056897341:ℚ)/5000000000),((6325845633:ℚ)/10000000000),((30678281387:ℚ)/55300000000),((8725845633:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((397533089:ℚ)/625000000),((-21285511524272542355269091122967050571958642283556550693799:ℚ)/74915033360848808288574218750000000000000000000000000000000),((-5797551152602367141507149:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((779241771:ℚ)/1250000000),((6445947551:ℚ)/10000000000),((7774692397:ℚ)/14062500000),((1263706793:ℚ)/1975000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((380587829:ℚ)/625000000),((-1436630309745641116952604646501464625995477476374033:ℚ)/5078145217895507812500000000000000000000000000000000),((-5774264976594420744521741:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((3177012961:ℚ)/5000000000),((328300191:ℚ)/500000000),((31519090727:ℚ)/57200000000),((149433397:ℚ)/234375000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((181481729:ℚ)/312500000),((-274716834666349978650090344916645358831421559576587717:ℚ)/975084304809570312500000000000000000000000000000000000),((-14374594412616508253821:ℚ)/36100000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((51792579:ℚ)/80000000),((6686016723:ℚ)/10000000000),((511028053:ℚ)/930400000),((9086016723:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1102572051:ℚ)/2000000000),((-630633600087824695079365748329913733783829622078058715239139:ℚ)/2247268032831250000000000000000000000000000000000000000000000),((-301277388303879375195831:ℚ)/760000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3297037897:ℚ)/5000000000),((6805988397:ℚ)/10000000000),((32359265279:ℚ)/59100000000),((9205988397:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4162859:ℚ)/8000000),((-156249194100191055558035107515422583363751799748028105159237:ℚ)/558911333526516723632812500000000000000000000000000000000000),((-5697563614296705422414869:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((6714038297:ℚ)/10000000000),((7045815913:ℚ)/10000000000),((65558268079:ℚ)/122000000000),((9445815913:ℚ)/14775000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4876719833:ℚ)/10000000000),((-759296842793236115344421125847223822793921603577862750377:ℚ)/2778167278613281250000000000000000000000000000000000000000),((-5602948720921011054563229:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((3476924177:ℚ)/5000000000),((301002241:ℚ)/400000000),((3735385471:ℚ)/7200000000),((397002241:ℚ)/610000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((4153378601:ℚ)/10000000000),((-10040142321247846635341066257459480862844607688002849:ℚ)/38303043750000000000000000000000000000000000000000000),((-8640281836919082393421:ℚ)/23104000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((7433056701:ℚ)/10000000000),((377517961:ℚ)/400000000),((70591396907:ℚ)/160000000000),((473517961:ℚ)/648000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2099862719:ℚ)/10000000000),((-13469935085483901126414904564662407596574508052921:ℚ)/62985600000000000000000000000000000000000000000000),((-5795775082963969:ℚ)/15200000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((1869170681:ℚ)/2000000000),((13253021659:ℚ)/10000000000),((5598731589:ℚ)/14720000000),((15653021659:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1156228448168926317769461223770865078566209932784728671897:ℚ)/6612500000000000000000000000000000000000000000000000000000),((-61591:ℚ)/160000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC24
#check @N11Formalization.C450Source31GroupedC24.bound
#print axioms N11Formalization.C450Source31GroupedC24.valid0
#print axioms N11Formalization.C450Source31GroupedC24.valid1
#print axioms N11Formalization.C450Source31GroupedC24.valid2
#print axioms N11Formalization.C450Source31GroupedC24.valid3
#print axioms N11Formalization.C450Source31GroupedC24.valid4
#print axioms N11Formalization.C450Source31GroupedC24.valid5
#print axioms N11Formalization.C450Source31GroupedC24.valid6
#print axioms N11Formalization.C450Source31GroupedC24.valid7
#print axioms N11Formalization.C450Source31GroupedC24.valid8
#print axioms N11Formalization.C450Source31GroupedC24.valid9
#print axioms N11Formalization.C450Source31GroupedC24.valid10
#print axioms N11Formalization.C450Source31GroupedC24.valid11
#print axioms N11Formalization.C450Source31GroupedC24.bound
#print axioms N11Formalization.C450Source31GroupedC24.endpoint_checks
