import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((1246922347:ℚ)/2000000000),((3276833709:ℚ)/5000000000),((-550501127:ℚ)/49600000000),((673077653:ℚ)/9920000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3043923229:ℚ)/5000000000),((848541271346836601392171748028870383:ℚ)/30505984000000000000000000000000000000),((-9800681859268702849733557:ℚ)/73932800000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6476444991:ℚ)/10000000000),((6674421609:ℚ)/10000000000),((-1463264827:ℚ)/103000000000),((3123555009:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5506897143:ℚ)/10000000000),((783037112822576782669166076088742353913474062784694121:ℚ)/26677905273437500000000000000000000000000000000000000000),((-268910876241077310795013213:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((824655101:ℚ)/1250000000),((6795102741:ℚ)/10000000000),((-1825308223:ℚ)/104900000000),((375344899:ℚ)/6556250000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1039038313:ℚ)/2000000000),((224492965987718038687462285727130129703622766969455473189:ℚ)/7214504056250000000000000000000000000000000000000000000000),((-4389498687717039383407973:ℚ)/28880000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/16),((-1:ℚ)/8),((671796201:ℚ)/1000000000),((6855417157:ℚ)/10000000000),((-2006251471:ℚ)/106800000000),((96067933:ℚ)/1780000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4865690213:ℚ)/10000000000),((26892328330790401923692166827762739922572137002936715077:ℚ)/845962800000000000000000000000000000000000000000000000000),((-2929921534029456683158573:ℚ)/18483200000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((1355659181:ℚ)/2000000000),((6915714767:ℚ)/10000000000),((-2187144301:ℚ)/107750000000),((564340819:ℚ)/10775000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((293318097:ℚ)/625000000),((255047499383889464251051854022326851188775675300094759367:ℚ)/7818651464843750000000000000000000000000000000000000000000),((-11961682700675114112706853:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((6838612639:ℚ)/10000000000),((6975996023:ℚ)/10000000000),((-2367988069:ℚ)/108700000000),((2761387361:ℚ)/54350000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2257227119:ℚ)/5000000000),((16774602017088201578918552018622313432416991679465516383:ℚ)/501705274609375000000000000000000000000000000000000000000),((-845163140825118589989653:ℚ)/5120000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((689891267:ℚ)/1000000000),((3518130679:ℚ)/5000000000),((-1274392037:ℚ)/54825000000),((15888749:ℚ)/322500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4329031867:ℚ)/10000000000),((91109226175992773486548771838901722769484114550461637:ℚ)/2661368261718750000000000000000000000000000000000000000),((-3111776669153818225049797:ℚ)/18483200000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((1739799111:ℚ)/2500000000),((7156745927:ℚ)/10000000000),((-2910237781:ℚ)/110600000000),((660200889:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((32311751:ℚ)/78125000),((6211213639271491852416712811553059362887655257115129423:ℚ)/172563650000000000000000000000000000000000000000000000000),((-19828963781450344419822733:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((1415943383:ℚ)/2000000000),((3638585827:ℚ)/5000000000),((-1635757481:ℚ)/56250000000),((504056617:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((148866621:ℚ)/400000000),((57215314109726687977517244160905077697604282770538923:ℚ)/1525878906250000000000000000000000000000000000000000000),((-13178839884722566096285997:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((72001773:ℚ)/100000000),((3758929119:ℚ)/5000000000),((-1996787357:ℚ)/57200000000),((2181657:ℚ)/52000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1629050399:ℚ)/5000000000),((11936176876292757636708242460342317846779007125144271519:ℚ)/292420700000000000000000000000000000000000000000000000000),((-94661182569515610397:ℚ)/512000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((3720464861:ℚ)/5000000000),((3879171277:ℚ)/5000000000),((-2357513831:ℚ)/59100000000),((1079535139:ℚ)/29550000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((64049119:ℚ)/312500000),((6235389585621718888921425557353763470214711823768381797:ℚ)/143350743750000000000000000000000000000000000000000000000),((-91596099702970487962729733:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7681475617:ℚ)/10000000000),((4119388601:ℚ)/5000000000),((-3078165803:ℚ)/61000000000),((1918524383:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((17547260220211409901353679954266159316860138843885203481:ℚ)/354657812500000000000000000000000000000000000000000000000),((-2650937:ℚ)/12800000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((4081011107:ℚ)/5000000000),((5077644133:ℚ)/5000000000),((-5952932399:ℚ)/64800000000),((718988893:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((288130661162938491719359431624865110096551880390907439:ℚ)/3936600000000000000000000000000000000000000000000000000),((-2650937:ℚ)/12800000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((10078550471:ℚ)/10000000000),((6987284089:ℚ)/5000000000),((-11681852267:ℚ)/80000000000),((-478550471:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((22320337706689194203256566780229750269681:ℚ)/203136000000000000000000000000000000000000),((-2650937:ℚ)/12800000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC14
#check @N11Formalization.C450Source31GroupedC14.bound
#print axioms N11Formalization.C450Source31GroupedC14.valid0
#print axioms N11Formalization.C450Source31GroupedC14.valid1
#print axioms N11Formalization.C450Source31GroupedC14.valid2
#print axioms N11Formalization.C450Source31GroupedC14.valid3
#print axioms N11Formalization.C450Source31GroupedC14.valid4
#print axioms N11Formalization.C450Source31GroupedC14.valid5
#print axioms N11Formalization.C450Source31GroupedC14.valid6
#print axioms N11Formalization.C450Source31GroupedC14.valid7
#print axioms N11Formalization.C450Source31GroupedC14.valid8
#print axioms N11Formalization.C450Source31GroupedC14.valid9
#print axioms N11Formalization.C450Source31GroupedC14.valid10
#print axioms N11Formalization.C450Source31GroupedC14.valid11
#print axioms N11Formalization.C450Source31GroupedC14.valid12
#print axioms N11Formalization.C450Source31GroupedC14.valid13
#print axioms N11Formalization.C450Source31GroupedC14.bound
#print axioms N11Formalization.C450Source31GroupedC14.endpoint_checks
