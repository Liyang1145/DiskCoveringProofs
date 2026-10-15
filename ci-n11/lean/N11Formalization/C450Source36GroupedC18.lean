import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/16),((1:ℚ)/8),((1466850563:ℚ)/2500000000),((6207776119:ℚ)/10000000000),((6906850563:ℚ)/25750000000),((17407776119:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3443863847:ℚ)/5000000000),((-13232224516398599333608144054607769995483357985278372974323:ℚ)/51274933935546875000000000000000000000000000000000000000000),((-113010768279236442787654877:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((763857453:ℚ)/1250000000),((3164603019:ℚ)/5000000000),((3483857453:ℚ)/13112500000),((8764603019:ℚ)/25750000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((6367027839:ℚ)/10000000000),((-4772227087243416067334472405300451308711669583255513425813:ℚ)/18686199592958068847656250000000000000000000000000000000000),((-29100550172464026201090277:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((3116210311:ℚ)/5000000000),((6450537471:ℚ)/10000000000),((4665403437:ℚ)/17800000000),((17650537471:ℚ)/52450000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((304644303:ℚ)/500000000),((-1219565710569936367393700417418432021393886197835927190051917:ℚ)/4848428703556250000000000000000000000000000000000000000000000),((-117684354456610076419250637:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((1270775631:ℚ)/2000000000),((6571775803:ℚ)/10000000000),((5622775631:ℚ)/21740000000),((17771775803:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2903884851:ℚ)/5000000000),((-567438872801640344623277930359298941643973062647487190807511:ℚ)/2289028308584175000000000000000000000000000000000000000000000),((-6260528927923059863141127:ℚ)/24320000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((6475237893:ℚ)/10000000000),((207261301:ℚ)/312500000),((28235237893:ℚ)/109650000000),((557261301:ℚ)/1698437500),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2754965837:ℚ)/5000000000),((-100100457757343125878782573113094140857873397123523744175505199:ℚ)/405652140396368261718750000000000000000000000000000000000000000),((-471168906119918169818703:ℚ)/1805000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((3267941373:ℚ)/5000000000),((6692926031:ℚ)/10000000000),((14147941373:ℚ)/55300000000),((5964308677:ℚ)/18275000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5355568877:ℚ)/10000000000),((-3243868903450878381063683713957152364522659618908587051345951:ℚ)/13237362141518115234375000000000000000000000000000000000000000),((-121241470486789247568930477:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((1649126273:ℚ)/2500000000),((6753469569:ℚ)/10000000000),((7089126273:ℚ)/27887500000),((2564781367:ℚ)/7900000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2598570561:ℚ)/5000000000),((-6434493979962905480917623655138267289880611645855411083697:ℚ)/26437048725979232788085937500000000000000000000000000000000),((-121859644296721773006160077:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6657105531:ℚ)/10000000000),((1703498199:ℚ)/2500000000),((28417105531:ℚ)/112500000000),((4503498199:ℚ)/13943750000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5034259269:ℚ)/10000000000),((-62746265268232428313692250391269685093153032707357880216120577:ℚ)/259530270266532897949218750000000000000000000000000000000000000),((-7654610734345332871534957:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((6717684639:ℚ)/10000000000),((108359069:ℚ)/156250000),((28477684639:ℚ)/114400000000),((31484341:ℚ)/97656250),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2433235331:ℚ)/5000000000),((-1113896862557865622886675715785677853650904629139485436791:ℚ)/4678731200000000000000000000000000000000000000000000000000),((-479098934889919906063857:ℚ)/1805000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((273551243:ℚ)/400000000),((7055892913:ℚ)/10000000000),((1143951243:ℚ)/4652000000),((18255892913:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((902789241:ℚ)/2000000000),((-1512734430239691872961038545368376259883903690769067295083:ℚ)/6433409777680600000000000000000000000000000000000000000000),((-123850098892439514363106733:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6959798633:ℚ)/10000000000),((7176734041:ℚ)/10000000000),((9573266211:ℚ)/39400000000),((18376734041:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4133932163:ℚ)/10000000000),((-15016795821866092757631251494640471787741893292124981003849651:ℚ)/64630590707731250000000000000000000000000000000000000000000000),((-125034836264012750355787517:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7080741259:ℚ)/10000000000),((370910799:ℚ)/500000000),((28840741259:ℚ)/122000000000),((930910799:ℚ)/2955000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3717957237:ℚ)/10000000000),((-149394762651624783329013041548182108323724593302251765819093217:ℚ)/660667922175000000000000000000000000000000000000000000000000000),((-16484143667884643571503:ℚ)/60800000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7322416219:ℚ)/10000000000),((3950231679:ℚ)/5000000000),((29082416219:ℚ)/129600000000),((9550231679:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2711040723:ℚ)/10000000000),((-1817132302282641531688575115240155061450490750952778628381017:ℚ)/8437299033600000000000000000000000000000000000000000000000000),((-67374734344760071:ℚ)/243200000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((1561002819:ℚ)/2000000000),((1964490601:ℚ)/2000000000),((5913002819:ℚ)/32000000000),((1401496867:ℚ)/4320000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-4572867975157105451214888600905899786983275671658388429673:ℚ)/24883200000000000000000000000000000000000000000000000000000),((-4597709:ℚ)/16000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((9728061393:ℚ)/10000000000),((13648085053:ℚ)/10000000000),((31488061393:ℚ)/220800000000),((24848085053:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-3876798624214404904522970191514471197316733092436676984979:ℚ)/25229491200000000000000000000000000000000000000000000000000),((-4597709:ℚ)/16000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC18
#check @N11Formalization.C450Source36GroupedC18.bound
#print axioms N11Formalization.C450Source36GroupedC18.valid0
#print axioms N11Formalization.C450Source36GroupedC18.valid1
#print axioms N11Formalization.C450Source36GroupedC18.valid2
#print axioms N11Formalization.C450Source36GroupedC18.valid3
#print axioms N11Formalization.C450Source36GroupedC18.valid4
#print axioms N11Formalization.C450Source36GroupedC18.valid5
#print axioms N11Formalization.C450Source36GroupedC18.valid6
#print axioms N11Formalization.C450Source36GroupedC18.valid7
#print axioms N11Formalization.C450Source36GroupedC18.valid8
#print axioms N11Formalization.C450Source36GroupedC18.valid9
#print axioms N11Formalization.C450Source36GroupedC18.valid10
#print axioms N11Formalization.C450Source36GroupedC18.valid11
#print axioms N11Formalization.C450Source36GroupedC18.valid12
#print axioms N11Formalization.C450Source36GroupedC18.valid13
#print axioms N11Formalization.C450Source36GroupedC18.valid14
#print axioms N11Formalization.C450Source36GroupedC18.bound
#print axioms N11Formalization.C450Source36GroupedC18.endpoint_checks
