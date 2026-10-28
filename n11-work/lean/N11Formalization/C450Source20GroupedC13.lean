import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((629453123:ℚ)/1000000000),((1317060691:ℚ)/2000000000),((-741060691:ℚ)/4960000000),((-672359369:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1189717033:ℚ)/2000000000),((25866697456883082035283618186887267911558759168824033683:ℚ)/317573784375000000000000000000000000000000000000000000000),((-4685379152760897070239657:ℚ)/147865600000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6533533521:ℚ)/10000000000),((682431421:ℚ)/1000000000),((-394431421:ℚ)/2575000000),((-7440600563:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((268081147:ℚ)/500000000),((7905948637686731352539130085797645845308916763371400971339:ℚ)/98025939450000000000000000000000000000000000000000000000000),((-575930156546313257967721153:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6772427963:ℚ)/10000000000),((216993113:ℚ)/312500000),((-126993113:ℚ)/834375000),((-8157283889:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2355066263:ℚ)/5000000000),((84942861198691236999985204747816446115383350376287752324517:ℚ)/1071642466565625000000000000000000000000000000000000000000000),((-1893776060592605542479057:ℚ)/40960000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1722959579:ℚ)/2500000000),((7063220227:ℚ)/10000000000),((-4183220227:ℚ)/27175000000),((-2128878737:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4351167631:ℚ)/10000000000),((265830363251968799519208355687394894710551183056026261883:ℚ)/3365939095440673828125000000000000000000000000000000000000),((-46102509436209184450994553:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7011225797:ℚ)/10000000000),((7182637313:ℚ)/10000000000),((-4302637313:ℚ)/27650000000),((-8873677391:ℚ)/112500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3962114533:ℚ)/10000000000),((2269650632015416604875322950579758350244852933558657514211:ℚ)/28834605216979980468750000000000000000000000000000000000000),((-791711501354936447653626297:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((3565295789:ℚ)/5000000000),((7302032061:ℚ)/10000000000),((-1474010687:ℚ)/9375000000),((-355068259:ℚ)/4400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3533008769:ℚ)/10000000000),((62666982818452491878508252242831377804380201195165223:ℚ)/798600000000000000000000000000000000000000000000000000),((-211466921695046217199126793:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((7249936751:ℚ)/10000000000),((927675697:ℚ)/1250000000),((-567675697:ℚ)/3575000000),((-9589810253:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3046931717:ℚ)/10000000000),((4231230140272062403916356114384078393928346175328225278177:ℚ)/54073172553125000000000000000000000000000000000000000000000),((-900109152370693624935309633:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1473852467:ℚ)/2000000000),((1885189723:ℚ)/2500000000),((-1165189723:ℚ)/7268750000),((-1989557401:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2470429071:ℚ)/10000000000),((34698673065918750540118942478461458259620576341617506231:ℚ)/444578439950000000000000000000000000000000000000000000000),((-38177452537968840978763337:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((1872142321:ℚ)/2500000000),((7779408741:ℚ)/10000000000),((-1633136247:ℚ)/9850000000),((-2576426963:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((857260341:ℚ)/5000000000),((4113288782511084232345089309737687308383518679010253612203:ℚ)/52400691796875000000000000000000000000000000000000000000000),((-63053097431670274819197953:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((965891349:ℚ)/1250000000),((4128252411:ℚ)/5000000000),((-2688252411:ℚ)/15250000000),((-1377674047:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((21434867280182430163275148669463722483392201881867905999:ℚ)/270149175000000000000000000000000000000000000000000000000),((-73390307:ℚ)/1024000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8204065929:ℚ)/10000000000),((40651553:ℚ)/40000000),((-29131553:ℚ)/129600000),((-12452197787:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((88019329705798866359517638491054780245392145873783867983317:ℚ)/1036800000000000000000000000000000000000000000000000000000000),((-73390307:ℚ)/1024000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10109959897:ℚ)/10000000000),((13970366471:ℚ)/10000000000),((-11090366471:ℚ)/40000000000),((-18169879691:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2395481098601988311840226278619631683614535262360723372007:ℚ)/25229491200000000000000000000000000000000000000000000000000),((-73390307:ℚ)/1024000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC13
#check @N11Formalization.C450Source20GroupedC13.bound
#print axioms N11Formalization.C450Source20GroupedC13.valid0
#print axioms N11Formalization.C450Source20GroupedC13.valid1
#print axioms N11Formalization.C450Source20GroupedC13.valid2
#print axioms N11Formalization.C450Source20GroupedC13.valid3
#print axioms N11Formalization.C450Source20GroupedC13.valid4
#print axioms N11Formalization.C450Source20GroupedC13.valid5
#print axioms N11Formalization.C450Source20GroupedC13.valid6
#print axioms N11Formalization.C450Source20GroupedC13.valid7
#print axioms N11Formalization.C450Source20GroupedC13.valid8
#print axioms N11Formalization.C450Source20GroupedC13.valid9
#print axioms N11Formalization.C450Source20GroupedC13.valid10
#print axioms N11Formalization.C450Source20GroupedC13.valid11
#print axioms N11Formalization.C450Source20GroupedC13.bound
#print axioms N11Formalization.C450Source20GroupedC13.endpoint_checks
