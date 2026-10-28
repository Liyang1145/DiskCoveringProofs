import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((6059424839:ℚ)/10000000000),((1316367243:ℚ)/2000000000),((3513141613:ℚ)/17800000000),((5869101729:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1619999323:ℚ)/2500000000),((8338203500927801040778409040839362451:ℚ)/193310319411200000000000000000000000000),((-5104466628935439710411359:ℚ)/31129600000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6536430833:ℚ)/10000000000),((6820134707:ℚ)/10000000000),((11016430833:ℚ)/55300000000),((10020134707:ℚ)/35600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2677077771:ℚ)/5000000000),((130518160167962889981085876828946676532860683223494055878897:ℚ)/3233787973815000000000000000000000000000000000000000000000000),((-134193757889866869551578159:ℚ)/778240000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((135496597:ℚ)/200000000),((6939263627:ℚ)/10000000000),((25010733:ℚ)/125000000),((30417790881:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2351581671:ℚ)/5000000000),((592366810186630491279082645578044382532102338923358319:ℚ)/15099319375000000000000000000000000000000000000000000000),((-137481614239676422991980639:ℚ)/778240000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((344700323:ℚ)/500000000),((7058379903:ℚ)/10000000000),((568700323:ℚ)/2860000000),((10258379903:ℚ)/37500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4344394699:ℚ)/10000000000),((3283485444044813609492345431117349231861992767248713679879:ℚ)/84247283935546875000000000000000000000000000000000000000000),((-139090623294813753323508119:ℚ)/778240000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((3506584413:ℚ)/5000000000),((7177484157:ℚ)/10000000000),((5746584413:ℚ)/29075000000),((31132452471:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3955484649:ℚ)/10000000000),((117872325756175308536940997368321332249139867782170646171451:ℚ)/3042455182910000000000000000000000000000000000000000000000000),((-140698280898918043299514959:ℚ)/778240000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/8),((3:ℚ)/16),((142646353:ℚ)/200000000),((7237031959:ℚ)/10000000000),((232246353:ℚ)/1172500000),((31311095877:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3526438843:ℚ)/10000000000),((258790734806785234986865839049834070209296171119326049745429:ℚ)/6757948356794277343750000000000000000000000000000000000000000),((-142339913203020054704216071:ℚ)/778240000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((7191887191:ℚ)/10000000000),((1824144243:ℚ)/2500000000),((11671887191:ℚ)/59100000000),((1124633247:ℚ)/4187500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3292010179:ℚ)/10000000000),((19135982541862097377572683660030859468135201182532755879:ℚ)/500921256079673767089843750000000000000000000000000000000),((-8946428675002915563213359:ℚ)/48640000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((7251453589:ℚ)/10000000000),((463478681:ℚ)/625000000),((11731453589:ℚ)/60050000000),((663478681:ℚ)/2462500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1520135939:ℚ)/5000000000),((193586382154697759313710361123261334002024344360421975251:ℚ)/5048077542376556396484375000000000000000000000000000000000),((-562146799402463901878351:ℚ)/3040000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((368528863:ℚ)/500000000),((3767365219:ℚ)/5000000000),((592528863:ℚ)/3050000000),((16102095657:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((9622437:ℚ)/39062500),((2403639917984234739470401489698416465220655229547736852441:ℚ)/62948985540244140625000000000000000000000000000000000000000),((-36378310181294078568929551:ℚ)/194560000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((3744844619:ℚ)/5000000000),((7772844273:ℚ)/10000000000),((5984844619:ℚ)/31450000000),((539648079:ℚ)/2000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((213232727:ℚ)/1250000000),((2378592083324071634198035030107398073943560660274117463:ℚ)/61818906250000000000000000000000000000000000000000000000),((-18393633800108143:ℚ)/97280000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((30911521:ℚ)/40000000),((400546099:ℚ)/500000000),((48831521:ℚ)/259200000),((1681638297:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((286821837898485601893558794232545480410341512759418497:ℚ)/7503486112265625000000000000000000000000000000000000000),((-195659687:ℚ)/1024000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((1991507643:ℚ)/2500000000),((619659567:ℚ)/625000000),((3111507643:ℚ)/20000000000),((819659567:ℚ)/2700000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((12314263604015203290434517417857824880508651015157:ℚ)/288325195312500000000000000000000000000000000000000),((-195659687:ℚ)/1024000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9870117703:ℚ)/10000000000),((3429702671:ℚ)/2500000000),((623918161:ℚ)/4800000000),((12689108013:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((92780069535414230176046801494946167:ℚ)/1800000000000000000000000000000000000),((-195659687:ℚ)/1024000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source16 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC19
#check @N11Formalization.C450Source16GroupedC19.bound
#print axioms N11Formalization.C450Source16GroupedC19.valid0
#print axioms N11Formalization.C450Source16GroupedC19.valid1
#print axioms N11Formalization.C450Source16GroupedC19.valid2
#print axioms N11Formalization.C450Source16GroupedC19.valid3
#print axioms N11Formalization.C450Source16GroupedC19.valid4
#print axioms N11Formalization.C450Source16GroupedC19.valid5
#print axioms N11Formalization.C450Source16GroupedC19.valid6
#print axioms N11Formalization.C450Source16GroupedC19.valid7
#print axioms N11Formalization.C450Source16GroupedC19.valid8
#print axioms N11Formalization.C450Source16GroupedC19.valid9
#print axioms N11Formalization.C450Source16GroupedC19.valid10
#print axioms N11Formalization.C450Source16GroupedC19.valid11
#print axioms N11Formalization.C450Source16GroupedC19.valid12
#print axioms N11Formalization.C450Source16GroupedC19.bound
#print axioms N11Formalization.C450Source16GroupedC19.endpoint_checks
