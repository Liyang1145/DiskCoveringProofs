import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((6237285347:ℚ)/10000000000),((1626368841:ℚ)/2500000000),((-3279106523:ℚ)/24800000000),((-2717285347:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6081692159:ℚ)/10000000000),((54990841401926925154300897718046483124580070397022516699:ℚ)/1654030126953125000000000000000000000000000000000000000000),((276866021432871188933483:ℚ)/184832000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((6475255343:ℚ)/10000000000),((3371746633:ℚ)/5000000000),((-6915239899:ℚ)/51500000000),((-2955255343:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5509887817:ℚ)/10000000000),((1868252200379823924336137847233567236516736806928091749:ℚ)/56727974218750000000000000000000000000000000000000000000),((-543909393432284603786773:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((33565959:ℚ)/50000000),((1372497719:ℚ)/2000000000),((-2837493157:ℚ)/21360000000),((-15965959:ℚ)/271750000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2439548171:ℚ)/5000000000),((67918769291160570768811003211855787398838792936059:ℚ)/2093051692510986328125000000000000000000000000000000),((-353689601862169331648277:ℚ)/118292480000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((1366429711:ℚ)/2000000000),((698147547:ℚ)/1000000000),((-1454442641:ℚ)/10870000000),((-662429711:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4533911027:ℚ)/10000000000),((290239138326029024999369643792530963455507310772221359:ℚ)/8975837587841796875000000000000000000000000000000000000),((-121413365085430881716413:ℚ)/29573120000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((6951098189:ℚ)/10000000000),((7040965873:ℚ)/10000000000),((-14722897619:ℚ)/110600000000),((-3431098189:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2081168823:ℚ)/5000000000),((75255235753104140968673568638774270169171476902118209019:ℚ)/2342523304833602905273437500000000000000000000000000000000),((-15473113645987636415946853:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((7010570449:ℚ)/10000000000),((7100454321:ℚ)/10000000000),((-14901362963:ℚ)/111550000000),((-387841161:ℚ)/6250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1982174151:ℚ)/5000000000),((26660210081339446436291902066276241872539206559954433:ℚ)/831112265586853027343750000000000000000000000000000000),((-17121775937279276644388837:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((7070041063:ℚ)/10000000000),((7159940863:ℚ)/10000000000),((-15079822589:ℚ)/112500000000),((-3550041063:ℚ)/56725000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1878260731:ℚ)/5000000000),((51386473904419966287891436654899297044448514420881841:ℚ)/1604227904983520507812500000000000000000000000000000000),((-18770106515646374156387333:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((891188759:ℚ)/1250000000),((7219425549:ℚ)/10000000000),((-15258276647:ℚ)/113450000000),((-451188759:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3537119333:ℚ)/10000000000),((10363378909155659149619077224402018706938595974546173413:ℚ)/323975863427734375000000000000000000000000000000000000000),((-20418106539442363463489357:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((1437795503:ℚ)/2000000000),((3639454211:ℚ)/5000000000),((-7718362633:ℚ)/57200000000),((-244598501:ℚ)/3845000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3303832209:ℚ)/10000000000),((3962472307429308132053174937317464261399712860001:ℚ)/124035253690719604492187500000000000000000000000000),((-5516444278397910523953197:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7248443433:ℚ)/10000000000),((917298691:ℚ)/1250000000),((-1951896073:ℚ)/14418750000),((-3728443433:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3053474541:ℚ)/10000000000),((5653742343359808892540016361296334570861735822717360776293:ℚ)/177197171988720703125000000000000000000000000000000000000000),((-370517490578074249387917:ℚ)/46208000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-3:ℚ)/16),((-1:ℚ)/8),((3653953931:ℚ)/5000000000),((7397868911:ℚ)/10000000000),((-15793606733:ℚ)/116300000000),((-1893953931:ℚ)/29312500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((556287089:ℚ)/2000000000),((364637040784003249246860262044404111847133593139628120591:ℚ)/11441904789638519287109375000000000000000000000000000000000),((-25360134407402916518776997:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3683685419:ℚ)/5000000000),((7457346611:ℚ)/10000000000),((-15972039833:ℚ)/117250000000),((-641228473:ℚ)/9850000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1240293119:ℚ)/5000000000),((1393322776704487426872329841855496293626420080169894219:ℚ)/43770507043457031250000000000000000000000000000000000000),((-27006823164120661486062797:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7426832397:ℚ)/10000000000),((60610377:ℚ)/80000000),((-130631131:ℚ)/945600000),((-3906832397:ℚ)/60050000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2138797243:ℚ)/10000000000),((398616499334948288217311830442666683471136554020808876949:ℚ)/12497598244519042968750000000000000000000000000000000000000),((-1831480500500093171733:ℚ)/189267968000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((3772875699:ℚ)/5000000000),((3847620689:ℚ)/5000000000),((-8342862067:ℚ)/60050000000),((-2012875699:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((239106369:ℚ)/2000000000),((6945628991746835121719995068617113467128330968860076897:ℚ)/218209033203125000000000000000000000000000000000000000000),((-5257727399044191:ℚ)/486400000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((61317321:ℚ)/80000000),((1634192261:ℚ)/2000000000),((-3622576783:ℚ)/24400000000),((-33157321:ℚ)/518400000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3973828934636601402113506744048330323889767920969:ℚ)/122947891200000000000000000000000000000000000000000),((-11600371:ℚ)/1024000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((4070135967:ℚ)/5000000000),((10073155949:ℚ)/10000000000),((-23819467847:ℚ)/129600000000),((-2310135967:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((68915851885125372206377666195308515747012999795561374529:ℚ)/2025000000000000000000000000000000000000000000000000000000),((-11600371:ℚ)/1024000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((5021060947:ℚ)/5000000000),((13875730453:ℚ)/10000000000),((-35227191359:ℚ)/160000000000),((-3261060947:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((206245568640956182703532875442197345775005634801785503:ℚ)/5475150000000000000000000000000000000000000000000000000),((-11600371:ℚ)/1024000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC14
#check @N11Formalization.C450Source12GroupedC14.bound
#print axioms N11Formalization.C450Source12GroupedC14.valid0
#print axioms N11Formalization.C450Source12GroupedC14.valid1
#print axioms N11Formalization.C450Source12GroupedC14.valid2
#print axioms N11Formalization.C450Source12GroupedC14.valid3
#print axioms N11Formalization.C450Source12GroupedC14.valid4
#print axioms N11Formalization.C450Source12GroupedC14.valid5
#print axioms N11Formalization.C450Source12GroupedC14.valid6
#print axioms N11Formalization.C450Source12GroupedC14.valid7
#print axioms N11Formalization.C450Source12GroupedC14.valid8
#print axioms N11Formalization.C450Source12GroupedC14.valid9
#print axioms N11Formalization.C450Source12GroupedC14.valid10
#print axioms N11Formalization.C450Source12GroupedC14.valid11
#print axioms N11Formalization.C450Source12GroupedC14.valid12
#print axioms N11Formalization.C450Source12GroupedC14.valid13
#print axioms N11Formalization.C450Source12GroupedC14.valid14
#print axioms N11Formalization.C450Source12GroupedC14.valid15
#print axioms N11Formalization.C450Source12GroupedC14.valid16
#print axioms N11Formalization.C450Source12GroupedC14.bound
#print axioms N11Formalization.C450Source12GroupedC14.endpoint_checks
