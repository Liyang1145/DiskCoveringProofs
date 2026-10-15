import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((310046319:ℚ)/500000000),((840909171:ℚ)/1250000000),((-120909171:ℚ)/6200000000),((297953681:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((308246303:ℚ)/500000000),((1196440047444297346084584961613203:ℚ)/15252992000000000000000000000000000),((-12993147852258818014875001:ℚ)/110899200000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((1335852611:ℚ)/2000000000),((870781293:ℚ)/1250000000),((-50260431:ℚ)/2225000000),((365382463:ℚ)/7120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4973490669:ℚ)/10000000000),((256894735772425899461113424714120013179910760594870589:ℚ)/3383851200000000000000000000000000000000000000000000000),((-78197442919654192741550987:ℚ)/591462400000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((345912889:ℚ)/500000000),((7085701081:ℚ)/10000000000),((-1325701081:ℚ)/55300000000),((262087111:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4267951779:ℚ)/10000000000),((5656322888926809345255077722246284136637325708667833:ℚ)/75496596875000000000000000000000000000000000000000000),((-5165779017110664319673987:ℚ)/36966400000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((3518858467:ℚ)/5000000000),((3602564171:ℚ)/5000000000),((-722564171:ℚ)/28125000000),((2561141533:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1935398403:ℚ)/5000000000),((41489831129072638716594383684168317032035041848234112477:ℚ)/556182861328125000000000000000000000000000000000000000000),((-530507763009693727467246283:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7157152327:ℚ)/10000000000),((7324533291:ℚ)/10000000000),((-1564533291:ℚ)/57200000000),((5002847673:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((171528831:ℚ)/500000000),((86911806916255783319958359726980249227245429902476603513:ℚ)/1169682800000000000000000000000000000000000000000000000000),((-2177772386873243039165989763:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((3638282569:ℚ)/5000000000),((1488783403:ℚ)/2000000000),((-336783403:ℚ)/11630000000),((2441717431:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2927884723:ℚ)/10000000000),((34120689790791325466367744215259471935987902431124407893:ℚ)/460850902441406250000000000000000000000000000000000000000),((-558384035601555754087421667:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((1848989117:ℚ)/2500000000),((1920656199:ℚ)/2500000000),((-160218733:ℚ)/4925000000),((1191010883:ℚ)/29550000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2322448499:ℚ)/10000000000),((17906730828045348605341281921118047329494962964575706489:ℚ)/241904380078125000000000000000000000000000000000000000000),((-143082675909033535758617483:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((7634678739:ℚ)/10000000000),((8159826411:ℚ)/10000000000),((-2399826411:ℚ)/61000000000),((4525321261:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((105046048469489969229887157787819789952493272989687487669:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-165148217:ℚ)/1024000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((8111906749:ℚ)/10000000000),((1258316341:ℚ)/1250000000),((-538316341:ℚ)/8100000000),((449788139:ℚ)/14400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((132807036177325368372070472644140227406251565365619457:ℚ)/1749600000000000000000000000000000000000000000000000000),((-165148217:ℚ)/1024000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((10018691313:ℚ)/10000000000),((693719203:ℚ)/500000000),((-405719203:ℚ)/4000000000),((2141308687:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((42719691351171152102893228073150887949:ℚ)/512000000000000000000000000000000000000),((-165148217:ℚ)/1024000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC15
#check @N11Formalization.C450Source20GroupedC15.bound
#print axioms N11Formalization.C450Source20GroupedC15.valid0
#print axioms N11Formalization.C450Source20GroupedC15.valid1
#print axioms N11Formalization.C450Source20GroupedC15.valid2
#print axioms N11Formalization.C450Source20GroupedC15.valid3
#print axioms N11Formalization.C450Source20GroupedC15.valid4
#print axioms N11Formalization.C450Source20GroupedC15.valid5
#print axioms N11Formalization.C450Source20GroupedC15.valid6
#print axioms N11Formalization.C450Source20GroupedC15.valid7
#print axioms N11Formalization.C450Source20GroupedC15.valid8
#print axioms N11Formalization.C450Source20GroupedC15.valid9
#print axioms N11Formalization.C450Source20GroupedC15.bound
#print axioms N11Formalization.C450Source20GroupedC15.endpoint_checks
