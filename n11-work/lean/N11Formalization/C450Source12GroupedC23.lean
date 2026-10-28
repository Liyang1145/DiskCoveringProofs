import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((2997431311:ℚ)/5000000000),((6514692419:ℚ)/10000000000),((10592293933:ℚ)/26700000000),((52642846933:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6619458337:ℚ)/10000000000),((16372757618368172539553:ℚ)/1980250000000000000000000),((-14801248462658583647396299:ℚ)/92416000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((1617690889:ℚ)/2500000000),((6752547087:ℚ)/10000000000),((5653072667:ℚ)/13825000000),((54307829609:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((552116669:ℚ)/1000000000),((5895924740740245254119166492791:ℚ)/975156250000000000000000000000000),((-3773343142846116162356699:ℚ)/23104000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((6708667471:ℚ)/10000000000),((6871465417:ℚ)/10000000000),((23326002413:ℚ)/56250000000),((55140257919:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2445890117:ℚ)/5000000000),((10352125164714293905408295804969467005435866054460077603:ℚ)/2038408115625000000000000000000000000000000000000000000000),((-60959087854661910645413579:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((6827609171:ℚ)/10000000000),((218449317:ℚ)/312500000),((23682827513:ℚ)/57200000000),((1749145219:ℚ)/3515625000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2273764093:ℚ)/5000000000),((12229077276115696936585941647875316072510579999386774757:ℚ)/2468182146549224853515625000000000000000000000000000000000),((-61252227213833278605110179:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((6946544489:ℚ)/10000000000),((7049832493:ℚ)/10000000000),((24039633467:ℚ)/57675000000),((5126257041:ℚ)/10400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4177132173:ℚ)/10000000000),((880754656125341700452906046161214699122858319296596933019:ℚ)/194883017550000000000000000000000000000000000000000000000000),((-61545594692726212980791899:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((7006009853:ℚ)/10000000000),((7109285543:ℚ)/10000000000),((24218029559:ℚ)/58150000000),((56804998801:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((24874127:ℚ)/62500000),((5371474285857917615164811936692088712849984008698931855331:ℚ)/1201347054450236328125000000000000000000000000000000000000000),((-61692364207347760490387971:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/8),((7:ℚ)/16),((3532736869:ℚ)/5000000000),((3584368663:ℚ)/5000000000),((12198210607:ℚ)/29312500000),((28610580641:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((235804251:ℚ)/625000000),((39857752769413423910243825288302187687687343257736848573:ℚ)/9005794718542480468750000000000000000000000000000000000000),((-15459797756275015375724659:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((7124936179:ℚ)/10000000000),((7228187873:ℚ)/10000000000),((124745221:ℚ)/300000000),((57637315111:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3554453329:ℚ)/10000000000),((689949148296665283126598803288470997263878660721255687:ℚ)/157412275695800781250000000000000000000000000000000000000),((-171706579578698077151339:ℚ)/1024000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((7184397211:ℚ)/10000000000),((1821909303:ℚ)/2500000000),((24753191633:ℚ)/59575000000),((14513365121:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1661179947:ℚ)/5000000000),((82860499903732149295835051411972994486406002803687914756379:ℚ)/19079163086131494140625000000000000000000000000000000000000000),((-172113620215645692139259:ℚ)/1024000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((7243856869:ℚ)/10000000000),((3673542687:ℚ)/5000000000),((24931570607:ℚ)/60050000000),((29234798809:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3073485747:ℚ)/10000000000),((32058119934708894192679286058511430892855953490934039086377:ℚ)/7445917498674273300170898437500000000000000000000000000000000),((-62280016117128432746364659:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((456457199:ℚ)/625000000),((233311821:ℚ)/312500000),((1569371597:ℚ)/3812500000),((1853182747:ℚ)/3753125000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((17521001:ℚ)/62500000),((351643116952005045702198597770235245864810160740000219:ℚ)/76842023364555835723876953125000000000000000000000000000),((-243855753743021731005019:ℚ)/1444000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((1484445583:ℚ)/2000000000),((7703751097:ℚ)/10000000000),((5093336749:ℚ)/12580000000),((60966257679:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2167156077:ℚ)/10000000000),((5852654658913271249142022599904211360318269515619252441627:ℚ)/1150140750781250000000000000000000000000000000000000000000000),((-2508854392445573533033291:ℚ)/14786560000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((38300193:ℚ)/50000000),((7941507897:ℚ)/10000000000),((130900579:ℚ)/324000000),((62630555279:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((8436944714554152328183330937517016420984221479586719914261:ℚ)/1700790185446875000000000000000000000000000000000000000000000),((-10935209:ℚ)/64000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((987228879:ℚ)/1250000000),((4921561319:ℚ)/5000000000),((3361686637:ℚ)/10000000000),((4218992137:ℚ)/7200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((67608639432664790224756242481307:ℚ)/6250000000000000000000000000000000),((-10935209:ℚ)/64000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((612479359:ℚ)/625000000),((13645017219:ℚ)/10000000000),((2037438077:ℚ)/6900000000),((102555120533:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6856083694072349231299:ℚ)/396750000000000000000000),((-10935209:ℚ)/64000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC23
#check @N11Formalization.C450Source12GroupedC23.bound
#print axioms N11Formalization.C450Source12GroupedC23.valid0
#print axioms N11Formalization.C450Source12GroupedC23.valid1
#print axioms N11Formalization.C450Source12GroupedC23.valid2
#print axioms N11Formalization.C450Source12GroupedC23.valid3
#print axioms N11Formalization.C450Source12GroupedC23.valid4
#print axioms N11Formalization.C450Source12GroupedC23.valid5
#print axioms N11Formalization.C450Source12GroupedC23.valid6
#print axioms N11Formalization.C450Source12GroupedC23.valid7
#print axioms N11Formalization.C450Source12GroupedC23.valid8
#print axioms N11Formalization.C450Source12GroupedC23.valid9
#print axioms N11Formalization.C450Source12GroupedC23.valid10
#print axioms N11Formalization.C450Source12GroupedC23.valid11
#print axioms N11Formalization.C450Source12GroupedC23.valid12
#print axioms N11Formalization.C450Source12GroupedC23.valid13
#print axioms N11Formalization.C450Source12GroupedC23.valid14
#print axioms N11Formalization.C450Source12GroupedC23.bound
#print axioms N11Formalization.C450Source12GroupedC23.endpoint_checks
