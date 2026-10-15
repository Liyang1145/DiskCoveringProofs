import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((9:ℚ)/16),((5:ℚ)/8),((5227919381:ℚ)/10000000000),((5573535421:ℚ)/10000000000),((68811274429:ℚ)/103000000000),((7813535421:ℚ)/9920000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((40611323:ℚ)/50000000),((-113309109836695737623293096636123596295204230042787446027:ℚ)/314211635200000000000000000000000000000000000000000000000),((-1758629273956805493182681629:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5469054793:ℚ)/10000000000),((5814608653:ℚ)/10000000000),((70981493137:ℚ)/106800000000),((8054608653:ℚ)/10300000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7675522639:ℚ)/10000000000),((-82373018002815209809987962053406973898908183545304629151:ℚ)/227936022656250000000000000000000000000000000000000000000),((-1735756179318381531216012221:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1141985193:ℚ)/2000000000),((5935049559:ℚ)/10000000000),((14629866737:ℚ)/21740000000),((8175049559:ℚ)/10680000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7207574723:ℚ)/10000000000),((-517782305047494737580541814403179867778510444044017749299:ℚ)/1379342345400000000000000000000000000000000000000000000000),((-1727584553770310408469621189:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((5830271361:ℚ)/10000000000),((3027715583:ℚ)/5000000000),((10604634607:ℚ)/15800000000),((4147715583:ℚ)/5435000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6964240719:ℚ)/10000000000),((-232364513184354617749156915509816178246631570125693993:ℚ)/619292448345947265625000000000000000000000000000000000),((-428839703127721569218500341:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((743820109:ℚ)/1250000000),((95556261:ℚ)/156250000),((9414380981:ℚ)/13943750000),((130556261:ℚ)/172812500),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((671372643:ℚ)/1000000000),((-122520973755135415808240406167894231401083831327473:ℚ)/321260276085138320922851562500000000000000000000000),((-417723320173607703877849:ℚ)/902500000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((1202137117:ℚ)/2000000000),((3087878279:ℚ)/5000000000),((15171234053:ℚ)/22500000000),((4207878279:ℚ)/5577500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((329275603:ℚ)/500000000),((-7266353180115734635375736736616875697990545747007159:ℚ)/19062124542045593261718750000000000000000000000000000),((-426171212597992547122349029:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((30353987:ℚ)/50000000),((155897477:ℚ)/250000000),((381985883:ℚ)/567250000),((211897477:ℚ)/281250000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1291033033:ℚ)/2000000000),((-150259886877124401896789576544711258746058452933377:ℚ)/394368410110473632812500000000000000000000000000000),((-1061435242732688192939501:ℚ)/2310400000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6130896649:ℚ)/10000000000),((629602861:ℚ)/1000000000),((76938069841:ℚ)/114400000000),((853602861:ℚ)/1134500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3161275053:ℚ)/5000000000),((-248508078790409238015849417883060221025469002943826387:ℚ)/652528612729296875000000000000000000000000000000000000),((-16918293495342273201969149:ℚ)/36966400000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((1547745913:ℚ)/2500000000),((6356145479:ℚ)/10000000000),((19369713217:ℚ)/28837500000),((8596145479:ℚ)/11440000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3093758643:ℚ)/5000000000),((-160502302338679629325303837789861564001415263788762933:ℚ)/421634096812500000000000000000000000000000000000000000),((-1685283749112591425899043429:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((3125529359:ℚ)/5000000000),((3208125001:ℚ)/5000000000),((39009764231:ℚ)/58150000000),((4328125001:ℚ)/5767500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((6049901043:ℚ)/10000000000),((-29478475514038683154227547663346424492405839221972242067:ℚ)/77472939882861328125000000000000000000000000000000000000),((-419664900625017391535192069:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((9:ℚ)/16),((5:ℚ)/8),((1577780537:ℚ)/2500000000),((647634249:ℚ)/1000000000),((293134699:ℚ)/437500000),((871634249:ℚ)/1163000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1181903419:ℚ)/2000000000),((-39262503462420330552702354983736328048462201317818149:ℚ)/103230602146875000000000000000000000000000000000000000),((-16719569237287702712728069:ℚ)/36966400000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6371174231:ℚ)/10000000000),((6536423237:ℚ)/10000000000),((79100568079:ℚ)/118200000000),((8776423237:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2883079737:ℚ)/5000000000),((-282947243942745170815675710937395916895408150088077239907:ℚ)/744245239489746093750000000000000000000000000000000000000),((-1665175727252756461722711661:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1286243049:ℚ)/2000000000),((6656550653:ℚ)/10000000000),((15928187441:ℚ)/24020000000),((8896550653:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5619596757:ℚ)/10000000000),((-1740282670865601205090738049200058329091663136371861220599:ℚ)/4648434567581250000000000000000000000000000000000000000000),((-1649514434412944008245400221:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((3275632573:ℚ)/5000000000),((6776634441:ℚ)/10000000000),((40360693157:ℚ)/61000000000),((9016634441:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5315773949:ℚ)/10000000000),((-370751195073218212410674975844012216984969535375216458607:ℚ)/990672559321875000000000000000000000000000000000000000000),((-1635403272737320105494493189:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((833909239:ℚ)/1250000000),((877084901:ℚ)/1250000000),((10225183151:ℚ)/15725000000),((1157084901:ℚ)/1525000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1248869863:ℚ)/2500000000),((-633437432757438170366419479288011769341186201171879329:ℚ)/1742810656738281250000000000000000000000000000000000000),((-25039304964740200850948269:ℚ)/57760000000000000000000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((6911175647:ℚ)/10000000000),((7256572479:ℚ)/10000000000),((83960580823:ℚ)/129600000000),((9496572479:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((858081491:ℚ)/2000000000),((-4954690215471816507710408011118573797431552365428148563:ℚ)/13619941425000000000000000000000000000000000000000000000),((-1572099328167496905067597429:ℚ)/3696640000000000000000000000)⟩
theorem valid15 : Valid source36 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source36 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7150934523:ℚ)/10000000000),((9171580149:ℚ)/10000000000),((86118410707:ℚ)/160000000000),((11411580149:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((345481691:ℚ)/1000000000),((-287634241927266332075286227657951151152892598088405023:ℚ)/1275458400000000000000000000000000000000000000000000000),((-100205421257638479:ℚ)/243200000000000000)⟩
theorem valid16 : Valid source36 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((4532550929:ℚ)/5000000000),((202954891:ℚ)/156250000),((51672958361:ℚ)/110400000000),((237954891:ℚ)/250000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-15090906964529698240551485075453:ℚ)/134765625000000000000000000000000),((-106444727:ℚ)/256000000)⟩
theorem valid17 : Valid source36 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source36 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source36 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source36 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source36 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC26
#check @N11Formalization.C450Source36GroupedC26.bound
#print axioms N11Formalization.C450Source36GroupedC26.valid0
#print axioms N11Formalization.C450Source36GroupedC26.valid1
#print axioms N11Formalization.C450Source36GroupedC26.valid2
#print axioms N11Formalization.C450Source36GroupedC26.valid3
#print axioms N11Formalization.C450Source36GroupedC26.valid4
#print axioms N11Formalization.C450Source36GroupedC26.valid5
#print axioms N11Formalization.C450Source36GroupedC26.valid6
#print axioms N11Formalization.C450Source36GroupedC26.valid7
#print axioms N11Formalization.C450Source36GroupedC26.valid8
#print axioms N11Formalization.C450Source36GroupedC26.valid9
#print axioms N11Formalization.C450Source36GroupedC26.valid10
#print axioms N11Formalization.C450Source36GroupedC26.valid11
#print axioms N11Formalization.C450Source36GroupedC26.valid12
#print axioms N11Formalization.C450Source36GroupedC26.valid13
#print axioms N11Formalization.C450Source36GroupedC26.valid14
#print axioms N11Formalization.C450Source36GroupedC26.valid15
#print axioms N11Formalization.C450Source36GroupedC26.valid16
#print axioms N11Formalization.C450Source36GroupedC26.valid17
#print axioms N11Formalization.C450Source36GroupedC26.bound
#print axioms N11Formalization.C450Source36GroupedC26.endpoint_checks
