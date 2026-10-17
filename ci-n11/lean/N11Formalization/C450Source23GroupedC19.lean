import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((5974448263:ℚ)/10000000000),((6517767551:ℚ)/10000000000),((12694448263:ℚ)/53400000000),((33633302653:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6663037699:ℚ)/10000000000),((148806959177830836782710417056069142501091:ℚ)/1449827395584000000000000000000000000000000),((-579116063831912889922202229:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1290759041:ℚ)/2000000000),((6757075581:ℚ)/10000000000),((2634759041:ℚ)/11060000000),((34351226743:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5563589247:ℚ)/10000000000),((55607064241921332822198148939052964820198424420235734755357129:ℚ)/582081835286700000000000000000000000000000000000000000000000000),((-613452305208582056035479069:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((3346620923:ℚ)/5000000000),((6876683293:ℚ)/10000000000),((6706620923:ℚ)/28125000000),((34710049879:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4934800521:ℚ)/10000000000),((251822582383902448121901207275201525874863008062203333711:ℚ)/2717877487500000000000000000000000000000000000000000000000),((-630557372978118396798889821:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((6812915271:ℚ)/10000000000),((3498131107:ℚ)/5000000000),((13532915271:ℚ)/57200000000),((17534393321:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4591349043:ℚ)/10000000000),((13453735561124175648377338433915930914729046519537537861017:ℚ)/145812606811523437500000000000000000000000000000000000000000),((-159551228175881141871696221:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1733139419:ℚ)/2500000000),((7115813777:ℚ)/10000000000),((3413139419:ℚ)/14537500000),((35427441331:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4222268849:ℚ)/10000000000),((6611426909340402577109347120423069427760630580660204192330167:ℚ)/71912577050600000000000000000000000000000000000000000000000000),((-645819878917691759827448341:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1763042651:ℚ)/2500000000),((7235339317:ℚ)/10000000000),((3443042651:ℚ)/14775000000),((35786017951:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((95502517:ℚ)/250000000),((6557428704327122027519528225570173498545971462733073258180139:ℚ)/71540650691394140625000000000000000000000000000000000000000000),((-653402393397384966959218381:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((896469437:ℚ)/1250000000),((1470968017:ℚ)/2000000000),((1736469437:ℚ)/7506250000),((7228904051:ℚ)/23640000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1686494023:ℚ)/5000000000),((2722425712466773474905724691388541482024296639568229368615773:ℚ)/29774772883547100000000000000000000000000000000000000000000000),((-26438102793708336891346581:ℚ)/73932800000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((3645656851:ℚ)/5000000000),((3737158627:ℚ)/5000000000),((7005656851:ℚ)/30500000000),((18251475881:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2859880673:ℚ)/10000000000),((114889125535970408437880776689306947835020769082515881154343:ℚ)/1258979710804882812500000000000000000000000000000000000000000),((-167117628688759861612430941:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((1482169297:ℚ)/2000000000),((318080437:ℚ)/400000000),((2826169297:ℚ)/12960000000),((1517441311:ℚ)/4880000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2235734857:ℚ)/10000000000),((1054994297056267058141375613128089287391377972006257459:ℚ)/11031276600000000000000000000000000000000000000000000000),((-35571328890608923:ℚ)/97280000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((394437301:ℚ)/500000000),((4930105369:ℚ)/5000000000),((730437301:ℚ)/4000000000),((21830316107:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2885330900033851401653319525740793005395106539738864661:ℚ)/26572050000000000000000000000000000000000000000000000000),((-47835429:ℚ)/128000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((4898785601:ℚ)/5000000000),((13669811253:ℚ)/10000000000),((8258785601:ℚ)/55200000000),((55089433759:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((55469608763997071600735945644706232803993:ℚ)/406272000000000000000000000000000000000000),((-47835429:ℚ)/128000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC19
#check @N11Formalization.C450Source23GroupedC19.bound
#print axioms N11Formalization.C450Source23GroupedC19.valid0
#print axioms N11Formalization.C450Source23GroupedC19.valid1
#print axioms N11Formalization.C450Source23GroupedC19.valid2
#print axioms N11Formalization.C450Source23GroupedC19.valid3
#print axioms N11Formalization.C450Source23GroupedC19.valid4
#print axioms N11Formalization.C450Source23GroupedC19.valid5
#print axioms N11Formalization.C450Source23GroupedC19.valid6
#print axioms N11Formalization.C450Source23GroupedC19.valid7
#print axioms N11Formalization.C450Source23GroupedC19.valid8
#print axioms N11Formalization.C450Source23GroupedC19.valid9
#print axioms N11Formalization.C450Source23GroupedC19.valid10
#print axioms N11Formalization.C450Source23GroupedC19.bound
#print axioms N11Formalization.C450Source23GroupedC19.endpoint_checks
