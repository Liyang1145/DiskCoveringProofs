import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/16),((1:ℚ)/8),((2985851641:ℚ)/5000000000),((3144134669:ℚ)/5000000000),((11305851641:ℚ)/51500000000),((7464134669:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1333775819:ℚ)/2000000000),((2369274360539666819147852141131859142483:ℚ)/40454748032000000000000000000000000000000),((-155605024081445058170633937:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6212694953:ℚ)/10000000000),((816100489:ℚ)/1250000000),((22852694953:ℚ)/106800000000),((1896100489:ℚ)/6437500000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6138092829:ℚ)/10000000000),((9004016242773824805128376558833442516860758732814807027:ℚ)/154772232180833816528320312500000000000000000000000000000),((-10024870577551549756070457:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6453433043:ℚ)/10000000000),((6648990177:ℚ)/10000000000),((23093433043:ℚ)/108700000000),((5096330059:ℚ)/17800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1391122883:ℚ)/2500000000),((6975151596812720622244515563574265150844607005078035395796277:ℚ)/124945427454150000000000000000000000000000000000000000000000000),((-662661800122320539143777193:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((821714441:ℚ)/1250000000),((6769126227:ℚ)/10000000000),((2901714441:ℚ)/13825000000),((15409126227:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5257205473:ℚ)/10000000000),((1071808246053067014068842058329477248123475297131815689595127:ℚ)/19178248540377294921875000000000000000000000000000000000000000),((-672136683144401936065848593:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6693944371:ℚ)/10000000000),((861151833:ℚ)/1250000000),((7777981457:ℚ)/37500000000),((1941151833:ℚ)/6912500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4932848747:ℚ)/10000000000),((16511935763211010239030811518199827478778166908934411:ℚ)/294908581542968750000000000000000000000000000000000000),((-10649534966550344763786713:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((6814122357:ℚ)/10000000000),((3504628957:ℚ)/5000000000),((23454122357:ℚ)/114400000000),((7824628957:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4587763879:ℚ)/10000000000),((159605604668198460687179274940538971287763860793382529540937:ℚ)/2843345832824707031250000000000000000000000000000000000000000),((-172740682974877591722306033:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((86678151:ℚ)/125000000),((3564629119:ℚ)/5000000000),((294678151:ℚ)/1453750000),((7884629119:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4216825047:ℚ)/10000000000),((8352367507382040273286600908157769875336375231104639356762897:ℚ)/148319690166862500000000000000000000000000000000000000000000000),((-175078603645625764638076137:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((7054335959:ℚ)/10000000000),((7249217749:ℚ)/10000000000),((23694335959:ℚ)/118200000000),((15889217749:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3812450543:ℚ)/10000000000),((2022043998249866243070131569827489603107422249697467486488403:ℚ)/35770325345697070312500000000000000000000000000000000000000000),((-709625518385796646891176417:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7174376253:ℚ)/10000000000),((748902211:ℚ)/1000000000),((23814376253:ℚ)/122000000000),((1612902211:ℚ)/5910000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((840638147:ℚ)/2500000000),((843985712386630596015935164380453081121094842341793571837:ℚ)/14402019172331250000000000000000000000000000000000000000000),((-7166116580719625466670257:ℚ)/18483200000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((1482866881:ℚ)/2000000000),((1992055023:ℚ)/2500000000),((4810866881:ℚ)/25920000000),((4152055023:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((553735101:ℚ)/2500000000),((756185656556179581224617710677622989710519267198668809041:ℚ)/12119322436523437500000000000000000000000000000000000000000),((-2425955569382943:ℚ)/6080000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((493363261:ℚ)/625000000),((9880985373:ℚ)/10000000000),((1533363261:ℚ)/10000000000),((6173661791:ℚ)/21600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((925804945986040525877881018434190739079729059310215473:ℚ)/11809800000000000000000000000000000000000000000000000000),((-52306587:ℚ)/128000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((4903712753:ℚ)/5000000000),((13695909311:ℚ)/10000000000),((4407904251:ℚ)/36800000000),((22335909311:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((7397206146992446807885498556972656248857:ℚ)/67712000000000000000000000000000000000000),((-52306587:ℚ)/128000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC18
#check @N11Formalization.C450Source28GroupedC18.bound
#print axioms N11Formalization.C450Source28GroupedC18.valid0
#print axioms N11Formalization.C450Source28GroupedC18.valid1
#print axioms N11Formalization.C450Source28GroupedC18.valid2
#print axioms N11Formalization.C450Source28GroupedC18.valid3
#print axioms N11Formalization.C450Source28GroupedC18.valid4
#print axioms N11Formalization.C450Source28GroupedC18.valid5
#print axioms N11Formalization.C450Source28GroupedC18.valid6
#print axioms N11Formalization.C450Source28GroupedC18.valid7
#print axioms N11Formalization.C450Source28GroupedC18.valid8
#print axioms N11Formalization.C450Source28GroupedC18.valid9
#print axioms N11Formalization.C450Source28GroupedC18.valid10
#print axioms N11Formalization.C450Source28GroupedC18.valid11
#print axioms N11Formalization.C450Source28GroupedC18.bound
#print axioms N11Formalization.C450Source28GroupedC18.endpoint_checks
