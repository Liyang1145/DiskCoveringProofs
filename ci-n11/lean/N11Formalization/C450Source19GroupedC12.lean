import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((3167470599:ℚ)/5000000000),((1325212971:ℚ)/2000000000),((-890012971:ℚ)/3968000000),((-1727470599:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5853027047:ℚ)/10000000000),((32664856537331200727466704134139428706547068033408032107:ℚ)/413507531738281250000000000000000000000000000000000000000),((1786532237067082014803579:ℚ)/86640000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((328687079:ℚ)/500000000),((53631783:ℚ)/78125000),((-36631783:ℚ)/160937500),((-184687079:ℚ)/1335000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1051427433:ℚ)/2000000000),((29996881195212577884303718076800623147098824014223331:ℚ)/382913825976562500000000000000000000000000000000000000),((4184926133155826274113:ℚ)/288800000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3406224359:ℚ)/5000000000),((6984235467:ℚ)/10000000000),((-4808235467:ℚ)/21360000000),((-1966224359:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((918546811:ℚ)/2000000000),((107105255760213719213697405895888782639317454247300824533:ℚ)/1395367795007324218750000000000000000000000000000000000000),((240863294214927191830633:ℚ)/28880000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((3465885203:ℚ)/5000000000),((3551790671:ℚ)/5000000000),((-2463790671:ℚ)/10870000000),((-2025885203:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1056198989:ℚ)/2500000000),((64399055826548339779588981923427450353519689209995166349:ℚ)/841484773860168457031250000000000000000000000000000000000),((151817383932548761936737:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1762768079:ℚ)/2500000000),((1790811653:ℚ)/2500000000),((-1246811653:ℚ)/5530000000),((-1042768079:ℚ)/6971875000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((477996917:ℚ)/1250000000),((5550745760227617954336070270571993903707839320685218429:ℚ)/73203853276050090789794921875000000000000000000000000000),((15654080736760179588113:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((1777679043:ℚ)/2500000000),((112857921:ℚ)/156250000),((-78857921:ℚ)/348593750),((-352559681:ℚ)/2343750000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1803917227:ℚ)/5000000000),((159323564585960425071786277536494833516027687176430279:ℚ)/2103752922266721725463867187500000000000000000000000000),((13468049486141304773771:ℚ)/21660000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7170355457:ℚ)/10000000000),((7282562463:ℚ)/10000000000),((-5106562463:ℚ)/22500000000),((-4290355457:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((844637521:ℚ)/2500000000),((80900171716188664399086317192528854773963294237949273:ℚ)/1069485269989013671875000000000000000000000000000000000),((-106962243283909822114743:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7229990287:ℚ)/10000000000),((7342213291:ℚ)/10000000000),((-5166213291:ℚ)/22690000000),((-4349990287:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3133233003:ℚ)/10000000000),((25066712553236889030477010875271439323361496230656510013401:ℚ)/331751284150000000000000000000000000000000000000000000000000),((-285910539042816859103383:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3644810387:ℚ)/5000000000),((7461501337:ℚ)/10000000000),((-5285501337:ℚ)/22880000000),((-2204810387:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2867766213:ℚ)/10000000000),((18958956061865236069211306824758755175077509735434962733:ℚ)/249627572155761718750000000000000000000000000000000000000),((-116253897130589192865183:ℚ)/28880000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7408869147:ℚ)/10000000000),((7580771971:ℚ)/10000000000),((-5404771971:ℚ)/23260000000),((-1509623049:ℚ)/9850000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((224743941:ℚ)/1000000000),((131611161440297422648500152602315999450905537530260807521:ℚ)/1736634531054687500000000000000000000000000000000000000000),((-2471091266522428395964189:ℚ)/346560000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((37640507:ℚ)/50000000),((1563852857:ℚ)/2000000000),((-376217619:ℚ)/1576000000),((-23240507:ℚ)/152500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1376611509:ℚ)/10000000000),((1002430688156927077507395501848642237988603689229919:ℚ)/13100172949218750000000000000000000000000000000000000),((-29575223507991609643:ℚ)/2888000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((7766520583:ℚ)/10000000000),((8296073351:ℚ)/10000000000),((-6120073351:ℚ)/24400000000),((-4886520583:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5517069109765761823814688430726576939213012860235852207:ℚ)/70858800000000000000000000000000000000000000000000000000),((-775627:ℚ)/64000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((8243196391:ℚ)/10000000000),((10201583837:ℚ)/10000000000),((-8025583837:ℚ)/25920000000),((-5363196391:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((922861241204396849805486467103510649204697885678437842791:ℚ)/10800000000000000000000000000000000000000000000000000000000),((-775627:ℚ)/64000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((634268841:ℚ)/625000000),((14008041213:ℚ)/10000000000),((-11832041213:ℚ)/32000000000),((-151422947:ℚ)/1150000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((687437305990884311466059189944844608964418659887547:ℚ)/7129101562500000000000000000000000000000000000000000),((-775627:ℚ)/64000000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source19 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source19 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source19 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC12
#check @N11Formalization.C450Source19GroupedC12.bound
#print axioms N11Formalization.C450Source19GroupedC12.valid0
#print axioms N11Formalization.C450Source19GroupedC12.valid1
#print axioms N11Formalization.C450Source19GroupedC12.valid2
#print axioms N11Formalization.C450Source19GroupedC12.valid3
#print axioms N11Formalization.C450Source19GroupedC12.valid4
#print axioms N11Formalization.C450Source19GroupedC12.valid5
#print axioms N11Formalization.C450Source19GroupedC12.valid6
#print axioms N11Formalization.C450Source19GroupedC12.valid7
#print axioms N11Formalization.C450Source19GroupedC12.valid8
#print axioms N11Formalization.C450Source19GroupedC12.valid9
#print axioms N11Formalization.C450Source19GroupedC12.valid10
#print axioms N11Formalization.C450Source19GroupedC12.valid11
#print axioms N11Formalization.C450Source19GroupedC12.valid12
#print axioms N11Formalization.C450Source19GroupedC12.valid13
#print axioms N11Formalization.C450Source19GroupedC12.bound
#print axioms N11Formalization.C450Source19GroupedC12.endpoint_checks
