import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((187779829:ℚ)/312500000),((3268215419:ℚ)/5000000000),((287779829:ℚ)/1112500000),((4548215419:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6589233081:ℚ)/10000000000),((81566126600534033867567121154344593519:ℚ)/1887796088000000000000000000000000000000),((-11790734127183802006872121:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6486173709:ℚ)/10000000000),((1354965971:ℚ)/2000000000),((29058521127:ℚ)/110600000000),((1866965971:ℚ)/5340000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1370596267:ℚ)/2500000000),((17321681307045304137413146452002408289429884979048276794231:ℚ)/436561376465025000000000000000000000000000000000000000000000),((-1969207459551085829928201:ℚ)/9241600000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((6724668199:ℚ)/10000000000),((1378801293:ℚ)/2000000000),((3308222733:ℚ)/12500000000),((1890801293:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((151462049:ℚ)/312500000),((2885029148766175091871661971680747212276693470838237:ℚ)/75496596875000000000000000000000000000000000000000000),((-6031471564176254433816667:ℚ)/27724800000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((68438901:ℚ)/100000000),((7013168831:ℚ)/10000000000),((301316703:ℚ)/1144000000),((3191056277:ℚ)/9375000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2249255541:ℚ)/5000000000),((181565888596863235422430226598282880667547667913958117769:ℚ)/4786777496337890625000000000000000000000000000000000000000),((-2671455190830385613368059:ℚ)/12160000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((3481548117:ℚ)/5000000000),((1426463531:ℚ)/2000000000),((15244644351:ℚ)/58150000000),((1938463531:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4123117877:ℚ)/10000000000),((22352389860816301353535508143541451000912776986458020701991:ℚ)/593278760667450000000000000000000000000000000000000000000000),((-2050091036429681966418521:ℚ)/9241600000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3541143691:ℚ)/5000000000),((3625726797:ℚ)/5000000000),((5141143691:ℚ)/19700000000),((4905726797:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3712353337:ℚ)/10000000000),((10465168242364478274809918466294324646375929134184985197457:ℚ)/279455666763258361816406250000000000000000000000000000000000),((-38809611302386518703875547:ℚ)/173280000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7201464271:ℚ)/10000000000),((1474115453:ℚ)/2000000000),((31204392813:ℚ)/120100000000),((1986115453:ℚ)/5910000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3252806089:ℚ)/10000000000),((103968926413440191577386119268831592859741102787959777765553:ℚ)/2791384957832540625000000000000000000000000000000000000000000),((-2089570774919795634167849:ℚ)/9241600000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((3660313791:ℚ)/5000000000),((7489689243:ℚ)/10000000000),((15780941373:ℚ)/61000000000),((10049689243:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2719815189:ℚ)/10000000000),((11667136510302432918047146556326837849258248899731905478741:ℚ)/314744927701220703125000000000000000000000000000000000000000),((-158194925653011243287596267:ℚ)/693120000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1487955591:ℚ)/2000000000),((1545576051:ℚ)/2000000000),((6383866773:ℚ)/25160000000),((2057576051:ℚ)/6100000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2057004687:ℚ)/10000000000),((2636567498996298231658523273682994424888614761255207664933:ℚ)/70158585797656250000000000000000000000000000000000000000000),((-560279232250093:ℚ)/2432000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((7678042243:ℚ)/10000000000),((7966030577:ℚ)/10000000000),((3626014081:ℚ)/14400000000),((10526030577:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((293763125037832144299224567497391971602846156324382892191:ℚ)/7874028636328125000000000000000000000000000000000000000000),((-3735911:ℚ)/16000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7916261509:ℚ)/10000000000),((2467529427:ℚ)/2500000000),((33348784527:ℚ)/160000000000),((3107529427:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((13720773596805071046122614140602689852715504771825963:ℚ)/311391210937500000000000000000000000000000000000000000),((-3735911:ℚ)/16000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((982078153:ℚ)/1000000000),((683745467:ℚ)/500000000),((1302078153:ℚ)/7360000000),((811745467:ℚ)/2000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((29298528558844824775520624357711567:ℚ)/529000000000000000000000000000000000),((-3735911:ℚ)/16000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC20
#check @N11Formalization.C450Source17GroupedC20.bound
#print axioms N11Formalization.C450Source17GroupedC20.valid0
#print axioms N11Formalization.C450Source17GroupedC20.valid1
#print axioms N11Formalization.C450Source17GroupedC20.valid2
#print axioms N11Formalization.C450Source17GroupedC20.valid3
#print axioms N11Formalization.C450Source17GroupedC20.valid4
#print axioms N11Formalization.C450Source17GroupedC20.valid5
#print axioms N11Formalization.C450Source17GroupedC20.valid6
#print axioms N11Formalization.C450Source17GroupedC20.valid7
#print axioms N11Formalization.C450Source17GroupedC20.valid8
#print axioms N11Formalization.C450Source17GroupedC20.valid9
#print axioms N11Formalization.C450Source17GroupedC20.valid10
#print axioms N11Formalization.C450Source17GroupedC20.valid11
#print axioms N11Formalization.C450Source17GroupedC20.bound
#print axioms N11Formalization.C450Source17GroupedC20.endpoint_checks
