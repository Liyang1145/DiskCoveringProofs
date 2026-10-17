import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/16),((1:ℚ)/8),((5895101069:ℚ)/10000000000),((1557367393:ℚ)/2500000000),((26375101069:ℚ)/103000000000),((4197367393:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3415092297:ℚ)/5000000000),((-3971656745114718902473020563119117753699500192998526189298199:ℚ)/19689574631250000000000000000000000000000000000000000000000000),((-30169333103431360956576393:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3068937419:ℚ)/5000000000),((6350584273:ℚ)/10000000000),((13308937419:ℚ)/52450000000),((16910584273:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((630699659:ℚ)/1000000000),((-476740921860339027326907068107030003287501193065837595692003:ℚ)/2391833547898632812500000000000000000000000000000000000000000),((-497608504138539182255430953:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6259113871:ℚ)/10000000000),((6471612399:ℚ)/10000000000),((8913037957:ℚ)/35600000000),((17031612399:ℚ)/52450000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((6031240579:ℚ)/10000000000),((-15214092845553473105931568257909538015852089840852494185235461:ℚ)/77574859256900000000000000000000000000000000000000000000000000),((-1510325182024087743082142971:ℚ)/5544960000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3190130821:ℚ)/5000000000),((3296279331:ℚ)/5000000000),((13430130821:ℚ)/54350000000),((2858759777:ℚ)/8900000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2872095167:ℚ)/5000000000),((-1534656927694858534644500177021145149577917808649163820523837:ℚ)/7948014960361718750000000000000000000000000000000000000000000),((-381908136238927121990212531:ℚ)/1386240000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6501323127:ℚ)/10000000000),((6713427433:ℚ)/10000000000),((26981323127:ℚ)/110600000000),((17273427433:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5444018039:ℚ)/10000000000),((-89077833551539760805897853523267008091826020773532572349006653:ℚ)/468323301983233593750000000000000000000000000000000000000000000),((-514916237367786592416347673:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6622302941:ℚ)/10000000000),((854277847:ℚ)/1250000000),((27102302941:ℚ)/112500000000),((310611121:ℚ)/987500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2564188959:ℚ)/5000000000),((-1544454208860646157110055385467994554052416342872339755449:ℚ)/8238458633422851562500000000000000000000000000000000000000),((-8133722467035769526899113:ℚ)/28880000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((6743205377:ℚ)/10000000000),((3477474237:ℚ)/5000000000),((27223205377:ℚ)/114400000000),((973052693:ℚ)/3125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((299635793:ℚ)/625000000),((-1729884300694810182595844654127810177780236211725038319641:ℚ)/9357462400000000000000000000000000000000000000000000000000),((-394602876985079038288109299:ℚ)/1386240000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3432017213:ℚ)/5000000000),((1768902013:ℚ)/2500000000),((13672017213:ℚ)/58150000000),((4408902013:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4437164769:ℚ)/10000000000),((-4583593067979318870542207446159694977932564710979995741240349:ℚ)/25130506944064843750000000000000000000000000000000000000000000),((-33228333038283694523076433:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((698479381:ℚ)/1000000000),((1124407:ℚ)/1562500),((915493127:ℚ)/3940000000),((5548814:ℚ)/18171875),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4051283507:ℚ)/10000000000),((-118129990205908519529635978732496101725442639987122194867:ℚ)/656148129012500000000000000000000000000000000000000000000),((-419614838067915357501:ℚ)/1444000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7105487:ℚ)/10000000),((929652737:ℚ)/1250000000),((27585487:ℚ)/122000000),((2249652737:ℚ)/7387500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((725455089:ℚ)/2000000000),((-231067132004620502726836268349906721903748845860580517:ℚ)/1321335844350000000000000000000000000000000000000000000),((-8420098190272244409799433:ℚ)/28880000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((3673343779:ℚ)/5000000000),((1979656221:ℚ)/2500000000),((13913343779:ℚ)/64800000000),((4619656221:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2589108059:ℚ)/10000000000),((-349850677112446824478535321303536513846311347851279541350801:ℚ)/2109324758400000000000000000000000000000000000000000000000000),((-36302039641246933:ℚ)/121600000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((7828423857:ℚ)/10000000000),((983806433:ℚ)/1000000000),((28308423857:ℚ)/160000000000),((2039806433:ℚ)/6480000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-2593930828656694643129696510789923790529605722469398796615009:ℚ)/18662400000000000000000000000000000000000000000000000000000000),((-39512983:ℚ)/128000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((2437217583:ℚ)/2500000000),((13660742341:ℚ)/10000000000),((7557217583:ℚ)/55200000000),((24220742341:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-88526894231041556198693835034172970655018218177577235677:ℚ)/788421600000000000000000000000000000000000000000000000000),((-39512983:ℚ)/128000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC18
#check @N11Formalization.C450Source34GroupedC18.bound
#print axioms N11Formalization.C450Source34GroupedC18.valid0
#print axioms N11Formalization.C450Source34GroupedC18.valid1
#print axioms N11Formalization.C450Source34GroupedC18.valid2
#print axioms N11Formalization.C450Source34GroupedC18.valid3
#print axioms N11Formalization.C450Source34GroupedC18.valid4
#print axioms N11Formalization.C450Source34GroupedC18.valid5
#print axioms N11Formalization.C450Source34GroupedC18.valid6
#print axioms N11Formalization.C450Source34GroupedC18.valid7
#print axioms N11Formalization.C450Source34GroupedC18.valid8
#print axioms N11Formalization.C450Source34GroupedC18.valid9
#print axioms N11Formalization.C450Source34GroupedC18.valid10
#print axioms N11Formalization.C450Source34GroupedC18.valid11
#print axioms N11Formalization.C450Source34GroupedC18.valid12
#print axioms N11Formalization.C450Source34GroupedC18.bound
#print axioms N11Formalization.C450Source34GroupedC18.endpoint_checks
