import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/8),((11:ℚ)/16),((332090913:ℚ)/625000000),((5648494433:ℚ)/10000000000),((448090913:ℚ)/643750000),((81333438763:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7966040901:ℚ)/10000000000),((-21031164115796269825678188141031009152702649514972560741624321:ℚ)/64727596851200000000000000000000000000000000000000000000000000),((-167533435720304654698518827:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((2169237:ℚ)/3906250),((5888293433:ℚ)/10000000000),((2894237:ℚ)/4171875),((83971227763:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7514637191:ℚ)/10000000000),((-13166629285601808076194091825753386432900763726958032531980107:ℚ)/40572612032812500000000000000000000000000000000000000000000000),((-165208772217447996081480827:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((5792873523:ℚ)/10000000000),((6008131819:ℚ)/10000000000),((7648873523:ℚ)/10870000000),((85289450009:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((440037661:ℚ)/625000000),((-111082071223461135733733472436054821113267420360511069248004481:ℚ)/333187806544400000000000000000000000000000000000000000000000000),((-164113207306404250006611923:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((2956315223:ℚ)/5000000000),((6127932313:ℚ)/10000000000),((3884315223:ℚ)/5530000000),((86607255443:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6793556977:ℚ)/10000000000),((-12770100909694543719506079131071378097416700641440812510450889:ℚ)/38356497080754589843750000000000000000000000000000000000000000),((-162885982657801544274209467:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((6032352347:ℚ)/10000000000),((6247696867:ℚ)/10000000000),((7888352347:ℚ)/11250000000),((87924665537:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1307757097:ℚ)/2000000000),((-42358753778407987706783714046175382914822760073830590751:ℚ)/127400507226562500000000000000000000000000000000000000000),((-161632823930615565745799427:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((615204103:ℚ)/1000000000),((3183713651:ℚ)/5000000000),((72800373:ℚ)/104000000),((44620850161:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1568829883:ℚ)/2500000000),((-770645986317126524162116324998043320834166858360494480403:ℚ)/2320861816406250000000000000000000000000000000000000000000),((-40088433783212732973684643:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6271698173:ℚ)/10000000000),((3243562659:ℚ)/5000000000),((8127698173:ℚ)/11630000000),((45279189249:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((60019863:ℚ)/100000000),((-47697080729803446775293123700387829457055932883312082216100233:ℚ)/143825154101200000000000000000000000000000000000000000000000000),((-39762179998719404070841283:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1597831337:ℚ)/2500000000),((3303396251:ℚ)/5000000000),((2061831337:ℚ)/2955000000),((45937358761:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2858671169:ℚ)/5000000000),((-11848118502103875055866785466830102401932755680040150532414889:ℚ)/35770325345697070312500000000000000000000000000000000000000000),((-39429445506004883311848243:ℚ)/92416000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6510924019:ℚ)/10000000000),((6726430339:ℚ)/10000000000),((8366924019:ℚ)/12010000000),((93190733729:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2709788361:ℚ)/5000000000),((-45604677856386562467546483254905112464860993787316023170761249:ℚ)/137846170757162500000000000000000000000000000000000000000000000),((-156360924492048304673588803:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((6630495559:ℚ)/10000000000),((3423020111:ℚ)/5000000000),((8486495559:ℚ)/12200000000),((47253221221:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5106364591:ℚ)/10000000000),((-1664180868554625765824516746753800359454429707892205544792127:ℚ)/5035918843219531250000000000000000000000000000000000000000000),((-38744537609344681376557003:ℚ)/92416000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1687510313:ℚ)/2500000000),((3542590629:ℚ)/5000000000),((2151510313:ℚ)/3145000000),((48568496919:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((954927211:ℚ)/2000000000),((-45245275808610190910608380170475423370166893366915012235592877:ℚ)/140317171595312500000000000000000000000000000000000000000000000),((-38007354479328702380803763:ℚ)/92416000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((3494529921:ℚ)/5000000000),((45776407:ℚ)/62500000),((4422529921:ℚ)/6480000000),((623540477:ℚ)/786250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4037018017:ℚ)/10000000000),((-115670538661976321584744008051656095739745576813332927:ℚ)/359119549291992187500000000000000000000000000000000000),((-11647073303092720871539:ℚ)/28880000000000000000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((7227988573:ℚ)/10000000000),((9233916861:ℚ)/10000000000),((9083988573:ℚ)/16000000000),((13419231719:ℚ)/14400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3141767019:ℚ)/10000000000),((-9826345619927114679512500834162034974821359071195799:ℚ)/43200000000000000000000000000000000000000000000000000),((-382947920194128359:ℚ)/972800000000000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9136958891:ℚ)/10000000000),((2609051743:ℚ)/2000000000),((10992958891:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-4268620696387984432338881:ℚ)/27084800000000000000000000),((-6312691:ℚ)/16000000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC27
#check @N11Formalization.C450Source31GroupedC27.bound
#print axioms N11Formalization.C450Source31GroupedC27.valid0
#print axioms N11Formalization.C450Source31GroupedC27.valid1
#print axioms N11Formalization.C450Source31GroupedC27.valid2
#print axioms N11Formalization.C450Source31GroupedC27.valid3
#print axioms N11Formalization.C450Source31GroupedC27.valid4
#print axioms N11Formalization.C450Source31GroupedC27.valid5
#print axioms N11Formalization.C450Source31GroupedC27.valid6
#print axioms N11Formalization.C450Source31GroupedC27.valid7
#print axioms N11Formalization.C450Source31GroupedC27.valid8
#print axioms N11Formalization.C450Source31GroupedC27.valid9
#print axioms N11Formalization.C450Source31GroupedC27.valid10
#print axioms N11Formalization.C450Source31GroupedC27.valid11
#print axioms N11Formalization.C450Source31GroupedC27.valid12
#print axioms N11Formalization.C450Source31GroupedC27.valid13
#print axioms N11Formalization.C450Source31GroupedC27.bound
#print axioms N11Formalization.C450Source31GroupedC27.endpoint_checks
