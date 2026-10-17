import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((3089077531:ℚ)/5000000000),((6687786797:ℚ)/10000000000),((992213203:ℚ)/106800000000),((13:ℚ)/155),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3108280063:ℚ)/5000000000),((144850757727209479867638000119:ℚ)/3539617665000000000000000000000),((-7884769929414291:ℚ)/121600000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((1663678623:ℚ)/2500000000),((6806838429:ℚ)/10000000000),((873161571:ℚ)/108700000000),((104:ℚ)/1335),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((630097099:ℚ)/1250000000),((8352429819654681241286912550028684428871549:ℚ)/210845408828878125000000000000000000000000000),((-4359131539787703:ℚ)/60800000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((6773820121:ℚ)/10000000000),((346293983:ℚ)/500000000),((37706017:ℚ)/5530000000),((416:ℚ)/5435),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((117652357:ℚ)/250000000),((362754929911465941454045361426083086618163:ℚ)/9205559299381101562500000000000000000000000),((-17853153004273281:ℚ)/243200000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((3446456739:ℚ)/5000000000),((7044911019:ℚ)/10000000000),((211696327:ℚ)/37500000000),((208:ℚ)/2765),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4347810233:ℚ)/10000000000),((138781340286229151611821916056989825500051:ℚ)/3538902978515625000000000000000000000000000),((-9134868461209179:ℚ)/121600000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((7011995189:ℚ)/10000000000),((7104423151:ℚ)/10000000000),((575576849:ℚ)/113450000000),((416:ℚ)/5625),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1979745259:ℚ)/5000000000),((1787010459825870571659632970652611755638303:ℚ)/45814882434082031250000000000000000000000000),((-18686280103309629:ℚ)/243200000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((7071531861:ℚ)/10000000000),((7163932999:ℚ)/10000000000),((516067001:ℚ)/114400000000),((832:ℚ)/11345),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3751171179:ℚ)/10000000000),((371931807459363294076177168407612943538949483:ℚ)/9555106981917640000000000000000000000000000000),((-18894537060035421:ℚ)/243200000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((1782766459:ℚ)/2500000000),((3611720309:ℚ)/5000000000),((228279691:ℚ)/57675000000),((4:ℚ)/55),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1765602387:ℚ)/5000000000),((8958342724677447249457841973310349023:ℚ)/230596139941406250000000000000000000000),((-4775696145690099:ℚ)/60800000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((7190597183:ℚ)/10000000000),((7282946063:ℚ)/10000000000),((397053937:ℚ)/116300000000),((832:ℚ)/11535),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((206078533:ℚ)/625000000),((134160331374615209347979510840522399038301179:ℚ)/3459879516816680625000000000000000000000000000),((-19311022912843863:ℚ)/243200000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/16),(0:ℚ),((3625062983:ℚ)/5000000000),((1835612347:ℚ)/2500000000),((12055379:ℚ)/4187500000),((416:ℚ)/5815),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3046101719:ℚ)/10000000000),((500471541058382741533227162392452265515787:ℚ)/12929748131621704101562500000000000000000000),((-9759626137077663:ℚ)/121600000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7309652247:ℚ)/10000000000),((7401950643:ℚ)/10000000000),((92683119:ℚ)/39400000000),((832:ℚ)/11725),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((173316487:ℚ)/625000000),((2886286376308984679521145386333499830773:ℚ)/74694081428750000000000000000000000000000),((-19727472883568367:ℚ)/243200000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((921147011:ℚ)/1250000000),((7520947143:ℚ)/10000000000),((159052857:ℚ)/120100000000),((208:ℚ)/2955),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2470893099:ℚ)/10000000000),((107783726023549759773261705398676953117480117:ℚ)/2791384957832540625000000000000000000000000000),((-2491960619744571:ℚ)/30400000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((7488216679:ℚ)/10000000000),((3819967971:ℚ)/5000000000),((20032029:ℚ)/61000000000),((416:ℚ)/6005),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((42930947:ℚ)/250000000),((77547725662846017015511596765764865842861721:ℚ)/2014367537287812500000000000000000000000000000),((-20352084302691519:ℚ)/243200000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((3803624093:ℚ)/5000000000),((1623173363:ℚ)/2000000000),((-87173363:ℚ)/24400000000),((104:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((106917270490858533104112492441513:ℚ)/2770764160156250000000000000000000),((-545871:ℚ)/6400000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((4041645703:ℚ)/5000000000),((2003804747:ℚ)/2000000000),((-467804747:ℚ)/25920000000),((26:ℚ)/405),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6073126893944292725293206383021:ℚ)/155695605468750000000000000000000),((-545871:ℚ)/6400000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((4993235423:ℚ)/5000000000),((6911368859:ℚ)/5000000000),((-3071368859:ℚ)/80000000000),((13:ℚ)/250),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3429733900218947:ℚ)/80000000000000000),((-545871:ℚ)/6400000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC16
#check @N11Formalization.C450Source14GroupedC16.bound
#print axioms N11Formalization.C450Source14GroupedC16.valid0
#print axioms N11Formalization.C450Source14GroupedC16.valid1
#print axioms N11Formalization.C450Source14GroupedC16.valid2
#print axioms N11Formalization.C450Source14GroupedC16.valid3
#print axioms N11Formalization.C450Source14GroupedC16.valid4
#print axioms N11Formalization.C450Source14GroupedC16.valid5
#print axioms N11Formalization.C450Source14GroupedC16.valid6
#print axioms N11Formalization.C450Source14GroupedC16.valid7
#print axioms N11Formalization.C450Source14GroupedC16.valid8
#print axioms N11Formalization.C450Source14GroupedC16.valid9
#print axioms N11Formalization.C450Source14GroupedC16.valid10
#print axioms N11Formalization.C450Source14GroupedC16.valid11
#print axioms N11Formalization.C450Source14GroupedC16.valid12
#print axioms N11Formalization.C450Source14GroupedC16.valid13
#print axioms N11Formalization.C450Source14GroupedC16.valid14
#print axioms N11Formalization.C450Source14GroupedC16.bound
#print axioms N11Formalization.C450Source14GroupedC16.endpoint_checks
