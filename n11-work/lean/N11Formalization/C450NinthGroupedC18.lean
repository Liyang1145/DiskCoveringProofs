import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6151865629:ℚ)/10000000000),((3325823859:ℚ)/5000000000),((10631865629:ℚ)/106800000000),((4605823859:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6275712591:ℚ)/10000000000),((4893504530853457126539439589494660100359:ℚ)/271842636672000000000000000000000000000000),((-721664122761337747770033173:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((165686129:ℚ)/250000000),((6770500099:ℚ)/10000000000),((277686129:ℚ)/2717500000),((9330500099:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1278642753:ℚ)/2500000000),((57567373063605517243293398348899857738849465487486217560576751:ℚ)/3373526541262050000000000000000000000000000000000000000000000000),((-476070622254265998100173:ℚ)/9241600000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6746327359:ℚ)/10000000000),((3444674479:ℚ)/5000000000),((11226327359:ℚ)/110600000000),((4724674479:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((74769677:ℚ)/156250000),((40612723297663590747995402100487217751243399569490225056793:ℚ)/2397281067547161865234375000000000000000000000000000000000000),((-2137783002988223555914213:ℚ)/40960000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6865205009:ℚ)/10000000000),((3504097237:ℚ)/5000000000),((3781735003:ℚ)/37500000000),((4784097237:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((443357561:ℚ)/1000000000),((2858503168537732966527500506559408216009357659115282213:ℚ)/169867342968750000000000000000000000000000000000000000000),((-781772155343561933826356493:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((349203917:ℚ)/500000000),((7067616031:ℚ)/10000000000),((573203917:ℚ)/5672500000),((9627616031:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2026835687:ℚ)/5000000000),((95505247552547526061715105852819273910060494467656896164092193:ℚ)/5726860304260253906250000000000000000000000000000000000000000000),((-1979526220293206853804917:ℚ)/36966400000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((3521756727:ℚ)/5000000000),((3563518407:ℚ)/5000000000),((5761756727:ℚ)/57200000000),((4843518407:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((770108347:ℚ)/2000000000),((149197532207727946897534433276518860553436470019563099037:ℚ)/8972268425027832031250000000000000000000000000000000000000),((-597623887961259158006251511:ℚ)/11089920000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((443934223:ℚ)/625000000),((3593228421:ℚ)/5000000000),((723934223:ℚ)/7209375000),((4873228421:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1818340347:ℚ)/5000000000),((1075356928879272704314271436681876549590992643813035604177881:ℚ)/64847324089762500000000000000000000000000000000000000000000000),((-3132244843674407983167437:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((7162380707:ℚ)/10000000000),((7245876133:ℚ)/10000000000),((11642380707:ℚ)/116300000000),((9805876133:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3410065577:ℚ)/10000000000),((357646608485390077670204585791294434753901912220170763515097:ℚ)/21624246980104253906250000000000000000000000000000000000000000),((-806878978249636771292635797:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/16),((1:ℚ)/8),((1444362579:ℚ)/2000000000),((3652647353:ℚ)/5000000000),((2340362579:ℚ)/23450000000),((4932647353:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((79198901:ℚ)/250000000),((418082556906285697999278601810450837642225585040491392880573:ℚ)/25342306337978540039062500000000000000000000000000000000000000),((-97428569685054936544789919:ℚ)/1774387200000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((1456248831:ℚ)/2000000000),((7364712577:ℚ)/10000000000),((2352248831:ℚ)/23640000000),((9924712577:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((726619441:ℚ)/2500000000),((1809720268955338271659671678467327159342817691352447569233719:ℚ)/109962234134609985351562500000000000000000000000000000000000000),((-98031838707539619146857799:ℚ)/1774387200000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((7340674509:ℚ)/10000000000),((1484825953:ℚ)/2000000000),((11820674509:ℚ)/119150000000),((665608651:ℚ)/3940000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2619832427:ℚ)/10000000000),((106931596468648511563390638204758915056221583067165068041439:ℚ)/6512354333399550000000000000000000000000000000000000000000000),((-2465882116802739572866128479:ℚ)/44359680000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((370005199:ℚ)/500000000),((1870886571:ℚ)/2500000000),((594005199:ℚ)/6005000000),((2510886571:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2298618007:ℚ)/10000000000),((30498151896061811272490994201038111773656540665912091088677:ℚ)/1861479374668568325042724609375000000000000000000000000000000),((-2067477245914546510975053:ℚ)/36966400000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7459532587:ℚ)/10000000000),((380118869:ℚ)/500000000),((11939532587:ℚ)/122000000000),((508118869:ℚ)/3002500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((962802441:ℚ)/5000000000),((10318897751432049506154499851253264881145458485018924603:ℚ)/629489855402441406250000000000000000000000000000000000000),((-832022569064004859763013957:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((3789193647:ℚ)/5000000000),((1615535593:ℚ)/2000000000),((6029193647:ℚ)/64800000000),((2127535593:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((754337589:ℚ)/10000000000),((308449371183378785947938213949936755614390420580567235559:ℚ)/18615279262500000000000000000000000000000000000000000000000),((-631567763393928270737624231:ℚ)/11089920000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((1006721923:ℚ)/1250000000),((1247324319:ℚ)/1250000000),((1566721923:ℚ)/20000000000),((1567324319:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((10666963487719694198035295482340755397419723128954491:ℚ)/622782421875000000000000000000000000000000000000000000),((-11688667:ℚ)/204800000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((9954958727:ℚ)/10000000000),((13779670229:ℚ)/10000000000),((4811652909:ℚ)/73600000000),((16339670229:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1323745646762646559258167683435276780809:ℚ)/67712000000000000000000000000000000000000),((-11688667:ℚ)/204800000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC18
#check @N11Formalization.C450NinthGroupedC18.bound
#print axioms N11Formalization.C450NinthGroupedC18.valid0
#print axioms N11Formalization.C450NinthGroupedC18.valid1
#print axioms N11Formalization.C450NinthGroupedC18.valid2
#print axioms N11Formalization.C450NinthGroupedC18.valid3
#print axioms N11Formalization.C450NinthGroupedC18.valid4
#print axioms N11Formalization.C450NinthGroupedC18.valid5
#print axioms N11Formalization.C450NinthGroupedC18.valid6
#print axioms N11Formalization.C450NinthGroupedC18.valid7
#print axioms N11Formalization.C450NinthGroupedC18.valid8
#print axioms N11Formalization.C450NinthGroupedC18.valid9
#print axioms N11Formalization.C450NinthGroupedC18.valid10
#print axioms N11Formalization.C450NinthGroupedC18.valid11
#print axioms N11Formalization.C450NinthGroupedC18.valid12
#print axioms N11Formalization.C450NinthGroupedC18.valid13
#print axioms N11Formalization.C450NinthGroupedC18.valid14
#print axioms N11Formalization.C450NinthGroupedC18.valid15
#print axioms N11Formalization.C450NinthGroupedC18.bound
#print axioms N11Formalization.C450NinthGroupedC18.endpoint_checks
