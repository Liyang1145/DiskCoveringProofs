import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((628804669:ℚ)/1000000000),((1314748317:ℚ)/2000000000),((-25895107:ℚ)/160000000),((-798414007:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5963793663:ℚ)/10000000000),((716596763673263028256522359950667512463976149145498007:ℚ)/10244315625000000000000000000000000000000000000000000000),((-87215149575104899407339:ℚ)/7393280000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6526731321:ℚ)/10000000000),((6812448723:ℚ)/10000000000),((-4252448723:ℚ)/25750000000),((-8700193963:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5379117853:ℚ)/10000000000),((6792789647050535282057996088961254806643642229226165867543:ℚ)/98025939450000000000000000000000000000000000000000000000000),((-12844499990004528935493859:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((1353066213:ℚ)/2000000000),((6931770411:ℚ)/10000000000),((-4371770411:ℚ)/26700000000),((-1883198639:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4730669009:ℚ)/10000000000),((583878657827326708709178365988507736526826887398138721279:ℚ)/8573139732525000000000000000000000000000000000000000000000),((-679018369428077263328731:ℚ)/29573120000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((860575239:ℚ)/1250000000),((7051072321:ℚ)/10000000000),((-4491072321:ℚ)/27175000000),((-1221725717:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1093425479:ℚ)/2500000000),((361471504628910627988605192922196430111021582602961229:ℚ)/5325852999114990234375000000000000000000000000000000000),((-297562105634296160423779:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((28015419:ℚ)/40000000),((7110716177:ℚ)/10000000000),((-650102311:ℚ)/3950000000),((-40526257:ℚ)/446200000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3987170621:ℚ)/10000000000),((92314409795270615106748992692057684646254679236429:ℚ)/1370710779514062500000000000000000000000000000000000),((-337832575780753741339:ℚ)/11829248000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((1412694941:ℚ)/2000000000),((3585177731:ℚ)/5000000000),((-2305177731:ℚ)/13943750000),((-2062084823:ℚ)/22500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1890000709:ℚ)/5000000000),((62585198455668752389681487047699486129975369451498829953:ℚ)/930632972717285156250000000000000000000000000000000000000),((-886023537328186568581419:ℚ)/29573120000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((3561545249:ℚ)/5000000000),((1807497573:ℚ)/2500000000),((-1167497573:ℚ)/7031250000),((-5244635747:ℚ)/56725000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((13911817:ℚ)/39062500),((861877630429992310952945553253829592488294594723921249:ℚ)/12833823239868164062500000000000000000000000000000000000),((-5796789457060990814410899:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((1436540447:ℚ)/2000000000),((7289620779:ℚ)/10000000000),((-4729620779:ℚ)/28362500000),((-2133621341:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((832297757:ℚ)/2500000000),((5695928510353382032215053199787291809888081244316399977627:ℚ)/84928328742400000000000000000000000000000000000000000000000),((-968969835705891613206291:ℚ)/29573120000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((56580547:ℚ)/78125000),((231527161:ℚ)/312500000),((-151527161:ℚ)/893750000),((-84741641:ℚ)/908593750),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3080206283:ℚ)/10000000000),((11275539152293584123300611599170151149771822844527863:ℚ)/167596636579185724258422851562500000000000000000000000),((-1541861221153114856891:ℚ)/45125000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1472302821:ℚ)/2000000000),((1505620281:ℚ)/2000000000),((-993620281:ℚ)/5815000000),((-2240908463:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((627945309:ℚ)/2500000000),((29836986136807850588777494876139832355264628075085934909:ℚ)/444578439950000000000000000000000000000000000000000000000),((-1093545529770644753040859:ℚ)/29573120000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((7480703513:ℚ)/10000000000),((1941630147:ℚ)/2500000000),((-1301630147:ℚ)/7387500000),((-11562110539:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((887077913:ℚ)/5000000000),((226446725845237121974208643690481038352207561025419841089847:ℚ)/3353644275000000000000000000000000000000000000000000000000000),((-29417521958011542692368931:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((1543808211:ℚ)/2000000000),((2060799099:ℚ)/2500000000),((-1420799099:ℚ)/7625000000),((-2455424633:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((75565640796427914957629195844361111003654231976218164997:ℚ)/1106531020800000000000000000000000000000000000000000000000),((-10907421:ℚ)/256000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8195568089:ℚ)/10000000000),((10148301461:ℚ)/10000000000),((-7588301461:ℚ)/32400000000),((-13706704267:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((75879386800192287062213299104189657767776507570267017255809:ℚ)/1036800000000000000000000000000000000000000000000000000000000),((-10907421:ℚ)/256000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((2525055109:ℚ)/2500000000),((3488571133:ℚ)/2500000000),((-2848571133:ℚ)/10000000000),((-4855165327:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((32255852113408879932603359337922971550572805344891120407:ℚ)/394210800000000000000000000000000000000000000000000000000),((-10907421:ℚ)/256000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC13
#check @N11Formalization.C450Source18GroupedC13.bound
#print axioms N11Formalization.C450Source18GroupedC13.valid0
#print axioms N11Formalization.C450Source18GroupedC13.valid1
#print axioms N11Formalization.C450Source18GroupedC13.valid2
#print axioms N11Formalization.C450Source18GroupedC13.valid3
#print axioms N11Formalization.C450Source18GroupedC13.valid4
#print axioms N11Formalization.C450Source18GroupedC13.valid5
#print axioms N11Formalization.C450Source18GroupedC13.valid6
#print axioms N11Formalization.C450Source18GroupedC13.valid7
#print axioms N11Formalization.C450Source18GroupedC13.valid8
#print axioms N11Formalization.C450Source18GroupedC13.valid9
#print axioms N11Formalization.C450Source18GroupedC13.valid10
#print axioms N11Formalization.C450Source18GroupedC13.valid11
#print axioms N11Formalization.C450Source18GroupedC13.valid12
#print axioms N11Formalization.C450Source18GroupedC13.valid13
#print axioms N11Formalization.C450Source18GroupedC13.bound
#print axioms N11Formalization.C450Source18GroupedC13.endpoint_checks
