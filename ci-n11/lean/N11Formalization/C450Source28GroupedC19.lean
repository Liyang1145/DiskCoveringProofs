import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/8),((3:ℚ)/16),((5906068263:ℚ)/10000000000),((3112133389:ℚ)/5000000000),((14226068263:ℚ)/51500000000),((17976400167:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6807288047:ℚ)/10000000000),((10023002015949609740328940789795054668481:ℚ)/323637984256000000000000000000000000000000),((-1323042845232064514644761819:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((122939783:ℚ)/200000000),((1616191243:ℚ)/2500000000),((289339783:ℚ)/1068000000),((9168573729:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6286631883:ℚ)/10000000000),((303885447930772340651215079449488729392109416575578938087:ℚ)/9905422859573364257812500000000000000000000000000000000000),((-17841927658061190063521769:ℚ)/48640000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6387661699:ℚ)/10000000000),((1316986807:ℚ)/2000000000),((14707661699:ℚ)/54350000000),((2468986807:ℚ)/7120000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1431561299:ℚ)/2500000000),((221525211287364587175338588037508418838544561394538190482209:ℚ)/7996507357065600000000000000000000000000000000000000000000000),((-223110530290218809138211411:ℚ)/591462400000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6507913197:ℚ)/10000000000),((1341010699:ℚ)/2000000000),((14827913197:ℚ)/55300000000),((7479032097:ℚ)/21740000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1356813033:ℚ)/2500000000),((34143497757867345446151857559195089506139000317277457340837:ℚ)/1227407906584146875000000000000000000000000000000000000000000),((-225697592200580832202673739:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6628112159:ℚ)/10000000000),((3412562961:ℚ)/5000000000),((1660901351:ℚ)/6250000000),((18877688883:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((40902221:ℚ)/80000000),((4223614179840529578056257401379334667684309141237378961:ℚ)/150993193750000000000000000000000000000000000000000000000),((-1426663733741917015461047619:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((6748261309:ℚ)/10000000000),((6945153711:ℚ)/10000000000),((15068261309:ℚ)/57200000000),((4235051237:ℚ)/12500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1194932537:ℚ)/2500000000),((7030440287408348694511082869244425207437024213557928550977:ℚ)/249621582031250000000000000000000000000000000000000000000000),((-5770410663213910003659623619:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6868363187:ℚ)/10000000000),((1413027819:ℚ)/2000000000),((15188363187:ℚ)/58150000000),((7695083457:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((884775733:ℚ)/2000000000),((718692072876206747575700412682046068780030641952198102204773:ℚ)/25313227121811200000000000000000000000000000000000000000000000),((-233348354797949963039699979:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((3494210081:ℚ)/5000000000),((7185084161:ℚ)/10000000000),((7654210081:ℚ)/29550000000),((38835252483:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4039160123:ℚ)/10000000000),((8199396907440706189104762325051179642692990193373820742673189:ℚ)/286162602765576562500000000000000000000000000000000000000000000),((-5896551308539360450307637219:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((1421686889:ℚ)/2000000000),((371243051:ℚ)/500000000),((3085686889:ℚ)/12200000000),((659243051:ℚ)/1970000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((723265947:ℚ)/2000000000),((16753210004450432179347339659751739953483030584798742277:ℚ)/533408117493750000000000000000000000000000000000000000000),((-14831217376639601792153739:ℚ)/36966400000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((183708577:ℚ)/250000000),((1976002241:ℚ)/2500000000),((391708577:ℚ)/1620000000),((10248006723:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((322573277:ℚ)/1250000000),((3532212377149847555610794148702377342952119920186994780741:ℚ)/96954579492187500000000000000000000000000000000000000000000),((-1247905400634069:ℚ)/3040000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((7827730769:ℚ)/10000000000),((1963324509:ℚ)/2000000000),((16147730769:ℚ)/80000000000),((1038441503:ℚ)/2880000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1617158460885987818430219121521936761951798427375601:ℚ)/27993600000000000000000000000000000000000000000000000),((-86637333:ℚ)/204800000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9741071099:ℚ)/10000000000),((13631369847:ℚ)/10000000000),((6020357033:ℚ)/36800000000),((58174109541:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((50629012537930932024257696042642385127787:ℚ)/541696000000000000000000000000000000000000),((-86637333:ℚ)/204800000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC19
#check @N11Formalization.C450Source28GroupedC19.bound
#print axioms N11Formalization.C450Source28GroupedC19.valid0
#print axioms N11Formalization.C450Source28GroupedC19.valid1
#print axioms N11Formalization.C450Source28GroupedC19.valid2
#print axioms N11Formalization.C450Source28GroupedC19.valid3
#print axioms N11Formalization.C450Source28GroupedC19.valid4
#print axioms N11Formalization.C450Source28GroupedC19.valid5
#print axioms N11Formalization.C450Source28GroupedC19.valid6
#print axioms N11Formalization.C450Source28GroupedC19.valid7
#print axioms N11Formalization.C450Source28GroupedC19.valid8
#print axioms N11Formalization.C450Source28GroupedC19.valid9
#print axioms N11Formalization.C450Source28GroupedC19.valid10
#print axioms N11Formalization.C450Source28GroupedC19.valid11
#print axioms N11Formalization.C450Source28GroupedC19.bound
#print axioms N11Formalization.C450Source28GroupedC19.endpoint_checks
