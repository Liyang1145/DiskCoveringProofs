import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6541031851:ℚ)/10000000000),((1350186357:ℚ)/2000000000),((-5739304499:ℚ)/19840000000),((-3341031851:ℚ)/16850000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2671138867:ℚ)/5000000000),((42449287182230378336540980449604273012931:ℚ)/221730182201344000000000000000000000000000),((168177551855933277312177897:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6661574221:ℚ)/10000000000),((858927347:ℚ)/1250000000),((-3692491429:ℚ)/12637500000),((-10384722663:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1004411547:ℚ)/2000000000),((178503733094950046344487797502951802683148421890516852367:ℚ)/929341819557952880859375000000000000000000000000000000000),((154754687644856651396725977:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6782049017:ℚ)/10000000000),((1732909487:ℚ)/2500000000),((-7490366409:ℚ)/25750000000),((-1194016339:ℚ)/5775000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2341079419:ℚ)/5000000000),((1411741445144838110055626394813048718642332616434344204201:ℚ)/7414373454666137695312500000000000000000000000000000000000),((141203936286447533489249633:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1368452453:ℚ)/2000000000),((1747960377:ℚ)/2500000000),((-7595722639:ℚ)/25987500000),((-2185357359:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2251717181:ℚ)/5000000000),((25111952972035695784829229986500709017436877758566361483:ℚ)/131653200695800781250000000000000000000000000000000000000),((5375221556125632290676873:ℚ)/73932800000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3451230007:ℚ)/5000000000),((7052029889:ℚ)/10000000000),((-30804209223:ℚ)/104900000000),((-5553690021:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4317892171:ℚ)/10000000000),((84632590440655043183247310931011958283144188077992546448289277:ℚ)/442920047525356250000000000000000000000000000000000000000000000),((31881273652162001499828353:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((1740660673:ℚ)/2500000000),((3556101753:ℚ)/5000000000),((-15612712271:ℚ)/52925000000),((-940660673:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2062303413:ℚ)/5000000000),((351199098153512867185877316996184509809976750047766883965773:ℚ)/1834774262465161132812500000000000000000000000000000000000000),((7539848775466926894169713:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((7022810711:ℚ)/10000000000),((7172362761:ℚ)/10000000000),((-31646539327:ℚ)/106800000000),((-11468432133:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1961214091:ℚ)/5000000000),((30132181593694737327173942627458336582067421178393257795593941:ℚ)/157146895690800000000000000000000000000000000000000000000000000),((113717974181211482423839937:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((7082964471:ℚ)/10000000000),((7232508039:ℚ)/10000000000),((-32067556273:ℚ)/107750000000),((-11648893413:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3709896697:ℚ)/10000000000),((1774457484407385393895781431735647224205500768310623088310015291:ℚ)/9238276192663964843750000000000000000000000000000000000000000000),((106766254270664654811566977:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3571552177:ℚ)/5000000000),((3646319857:ℚ)/5000000000),((-16244238999:ℚ)/54350000000),((-1971552177:ℚ)/9137500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((871278191:ℚ)/2500000000),((6447838223864140811216480817069299855125511561112989822934693:ℚ)/33511466530692529296875000000000000000000000000000000000000000),((24945600052118050938890513:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7203230731:ℚ)/10000000000),((1470551629:ℚ)/2000000000),((-2193953801:ℚ)/7310000000),((-12009692193:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1622762579:ℚ)/5000000000),((3346394350255678112838376216293736255781993412001745590649:ℚ)/17362567823956250000000000000000000000000000000000000000000),((92766391951342952529093417:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7263343959:ℚ)/10000000000),((7472956649:ℚ)/10000000000),((-33750696543:ℚ)/110600000000),((-4063343959:ℚ)/18750000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2987567629:ℚ)/10000000000),((101033523144116423635387054164316596464008269509156696863:ℚ)/517690950000000000000000000000000000000000000000000000000),((237446565828154675466137:ℚ)/5120000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((7383532329:ℚ)/10000000000),((949138273:ℚ)/1250000000),((-480440879:ℚ)/1562500000),((-12550596987:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2392439527:ℚ)/10000000000),((95447494816234705708749017136294708795996553477024380257:ℚ)/487542152404785156250000000000000000000000000000000000000),((71525253579307475797603777:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((7503672079:ℚ)/10000000000),((504578837:ℚ)/625000000),((-2372051859:ℚ)/7150000000),((-12911016237:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1593837641:ℚ)/10000000000),((442746586817136015525811949020186344076218404804916966297:ℚ)/2125190282617187500000000000000000000000000000000000000000),((57203389258114193526549777:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((7983791291:ℚ)/10000000000),((8552803251:ℚ)/10000000000),((-41309622757:ℚ)/122000000000),((-1594597097:ℚ)/7200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((16080107179340077549015023142716184779054767163612303064333:ℚ)/76606087500000000000000000000000000000000000000000000000000),((78987:ℚ)/3200000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((8463301499:ℚ)/10000000000),((10466610787:ℚ)/10000000000),((-54706275509:ℚ)/129600000000),((-15789904497:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((7912976356497326905995963591011882734681765859087340269:ℚ)/31492800000000000000000000000000000000000000000000000000),((78987:ℚ)/3200000)⟩
theorem valid14 : Valid source31 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((2594253281:ℚ)/2500000000),((714137391:ℚ)/500000000),((-4070961737:ℚ)/8000000000),((-1794253281:ℚ)/9200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((12803337600360167022434351:ℚ)/42320000000000000000000000),((78987:ℚ)/3200000)⟩
theorem valid15 : Valid source31 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC10
#check @N11Formalization.C450Source31GroupedC10.bound
#print axioms N11Formalization.C450Source31GroupedC10.valid0
#print axioms N11Formalization.C450Source31GroupedC10.valid1
#print axioms N11Formalization.C450Source31GroupedC10.valid2
#print axioms N11Formalization.C450Source31GroupedC10.valid3
#print axioms N11Formalization.C450Source31GroupedC10.valid4
#print axioms N11Formalization.C450Source31GroupedC10.valid5
#print axioms N11Formalization.C450Source31GroupedC10.valid6
#print axioms N11Formalization.C450Source31GroupedC10.valid7
#print axioms N11Formalization.C450Source31GroupedC10.valid8
#print axioms N11Formalization.C450Source31GroupedC10.valid9
#print axioms N11Formalization.C450Source31GroupedC10.valid10
#print axioms N11Formalization.C450Source31GroupedC10.valid11
#print axioms N11Formalization.C450Source31GroupedC10.valid12
#print axioms N11Formalization.C450Source31GroupedC10.valid13
#print axioms N11Formalization.C450Source31GroupedC10.valid14
#print axioms N11Formalization.C450Source31GroupedC10.valid15
#print axioms N11Formalization.C450Source31GroupedC10.bound
#print axioms N11Formalization.C450Source31GroupedC10.endpoint_checks
