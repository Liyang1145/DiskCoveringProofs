import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/16),((1:ℚ)/2),((2781829517:ℚ)/5000000000),((5891324521:ℚ)/10000000000),((28112806619:ℚ)/51500000000),((262300791:ℚ)/400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7494547861:ℚ)/10000000000),((-982035371405988429010670976253735111447989671816454699:ℚ)/4243600000000000000000000000000000000000000000000000000),((-5717465963025669924143519:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5804008659:ℚ)/10000000000),((3065737329:ℚ)/5000000000),((19302686871:ℚ)/35600000000),((4185737329:ℚ)/6437500000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1403587631:ℚ)/2000000000),((-757062157007310055116192079094233100355457835917808051949:ℚ)/3301807619857788085937500000000000000000000000000000000000),((-4268041720356768863970157:ℚ)/10830000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6044152101:ℚ)/10000000000),((39821499:ℚ)/62500000),((59589064707:ℚ)/110600000000),((53821499:ℚ)/83437500),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6513217949:ℚ)/10000000000),((-24228332037257344646301744511444571504121381638728139071:ℚ)/106582367301031494140625000000000000000000000000000000000),((-663252591846086922427:ℚ)/1692187500000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((6284111061:ℚ)/10000000000),((811419881:ℚ)/1250000000),((20422925809:ℚ)/37500000000),((1091419881:ℚ)/1728125000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1194601497:ℚ)/2000000000),((-67102770781600839080066555942281989116689393338056089:ℚ)/290300634956359863281250000000000000000000000000000000),((-88786501012415525431999:ℚ)/225625000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6404027321:ℚ)/10000000000),((6611238863:ℚ)/10000000000),((62108191247:ℚ)/114400000000),((8851238863:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2843189993:ℚ)/5000000000),((-5112376170554966024121609830415250920658977695966230929493:ℚ)/22213639318943023681640625000000000000000000000000000000000),((-5664204814743763993441871:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((203872009:ℚ)/312500000),((1682770313:ℚ)/2500000000),((1967104063:ℚ)/3634375000),((2242770313:ℚ)/3575000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2693186881:ℚ)/5000000000),((-8047374313727212291927110331779548519689469194968024490567:ℚ)/35113563012988281250000000000000000000000000000000000000000),((-352813882903533987768671:ℚ)/902500000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1660935981:ℚ)/2500000000),((137017761:ℚ)/200000000),((5315517289:ℚ)/9850000000),((181817761:ℚ)/290750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5070582349:ℚ)/10000000000),((-340196689386009111757527061249287926443161432537164429:ℚ)/1490430222737377929687500000000000000000000000000000000),((-6749746456079307011917:ℚ)/17328000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3381774031:ℚ)/5000000000),((3485330489:ℚ)/5000000000),((32312418217:ℚ)/60050000000),((1535110163:ℚ)/2462500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4735815591:ℚ)/10000000000),((-22954823113803592337436043976419296628475911514331992114621:ℚ)/100961550847531127929687500000000000000000000000000000000000),((-1400876309971085028144639:ℚ)/3610000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((1376663683:ℚ)/2000000000),((1418080329:ℚ)/2000000000),((13092645781:ℚ)/24400000000),((1866080329:ℚ)/3002500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((875537483:ℚ)/2000000000),((-427745440310633935272316647350569332075620005439627591827:ℚ)/1888469566207324218750000000000000000000000000000000000000),((-669740679368017523808157:ℚ)/1732800000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((7003056589:ℚ)/10000000000),((7569070511:ℚ)/10000000000),((66301396123:ℚ)/129600000000),((9809070511:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((997468709:ℚ)/2500000000),((-30755815435417458920117761450872238503862822106818211426891:ℚ)/145431869238281250000000000000000000000000000000000000000000),((-5362698320893251623642639:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((935214529:ℚ)/1250000000),((4740115549:ℚ)/5000000000),((8706501703:ℚ)/20000000000),((5860115549:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1766589559:ℚ)/10000000000),((-1653303043940706572868370420524889664293530554431228307:ℚ)/9964518750000000000000000000000000000000000000000000000),((-45260187472797:ℚ)/118750000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((2348212209:ℚ)/2500000000),((6646642857:ℚ)/5000000000),((6919161821:ℚ)/18400000000),((7766642857:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-317313524187178196625921761774635102148873667136880925751:ℚ)/2479687500000000000000000000000000000000000000000000000000),((-614153:ℚ)/1600000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC24
#check @N11Formalization.C450Source29GroupedC24.bound
#print axioms N11Formalization.C450Source29GroupedC24.valid0
#print axioms N11Formalization.C450Source29GroupedC24.valid1
#print axioms N11Formalization.C450Source29GroupedC24.valid2
#print axioms N11Formalization.C450Source29GroupedC24.valid3
#print axioms N11Formalization.C450Source29GroupedC24.valid4
#print axioms N11Formalization.C450Source29GroupedC24.valid5
#print axioms N11Formalization.C450Source29GroupedC24.valid6
#print axioms N11Formalization.C450Source29GroupedC24.valid7
#print axioms N11Formalization.C450Source29GroupedC24.valid8
#print axioms N11Formalization.C450Source29GroupedC24.valid9
#print axioms N11Formalization.C450Source29GroupedC24.valid10
#print axioms N11Formalization.C450Source29GroupedC24.valid11
#print axioms N11Formalization.C450Source29GroupedC24.bound
#print axioms N11Formalization.C450Source29GroupedC24.endpoint_checks
