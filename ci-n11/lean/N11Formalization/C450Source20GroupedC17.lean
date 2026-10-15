import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((305296319:ℚ)/500000000),((663605493:ℚ)/1000000000),((48:ℚ)/445),((1879605493:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((255117501:ℚ)/400000000),((70848616813304421548029008710656376951:ℚ)/966551597056000000000000000000000000000),((-83455079146054536143031791:ℚ)/443596800000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((1316852611:ℚ)/2000000000),((859362557:ℚ)/1250000000),((288:ℚ)/2765),((2379362557:ℚ)/13350000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5229484131:ℚ)/10000000000),((478838415735686816080302169519359182735945692665522583084319:ℚ)/6821271507266015625000000000000000000000000000000000000000000),((-46854914422355572307386197:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((341162889:ℚ)/500000000),((874286107:ℚ)/1250000000),((64:ℚ)/625),((2394286107:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((45605459:ℚ)/100000000),((81381560184170812024934148037661582669650567623467949:ℚ)/1179634326171875000000000000000000000000000000000000000),((-48547263143955261269857797:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((3471358467:ℚ)/5000000000),((1778413971:ℚ)/2500000000),((72:ℚ)/715),((4818413971:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1047382371:ℚ)/2500000000),((97542281925535766115418253088343195063069859252393093227219:ℚ)/1421672916412353515625000000000000000000000000000000000000000),((-592532445456350297018478719:ℚ)/2772480000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7062152327:ℚ)/10000000000),((7233002599:ℚ)/10000000000),((576:ℚ)/5815),((19393002599:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3784713193:ℚ)/10000000000),((324020755189748422326282737695851461008425398946863768481915277:ℚ)/4746230085339600000000000000000000000000000000000000000000000000),((-3213277693218837633228315453:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((3590782569:ℚ)/5000000000),((735232999:ℚ)/1000000000),((96:ℚ)/985),((1951232999:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3333766231:ℚ)/10000000000),((9723968173875783123561973788444143923940224535722951626493:ℚ)/143081301382788281250000000000000000000000000000000000000000),((-32663393373233521097813053:ℚ)/147865600000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((1825239117:ℚ)/2500000000),((933954873:ℚ)/1250000000),((576:ℚ)/6005),((2453954873:ℚ)/14775000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((56291113:ℚ)/200000000),((2952112635115071754213874157269960818111169861031011764898899:ℚ)/43615389966133447265625000000000000000000000000000000000000000),((-155594928867480127491691511:ℚ)/693120000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((3710163673:ℚ)/5000000000),((3795465223:ℚ)/5000000000),((144:ℚ)/1525),((9875465223:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2178755657:ℚ)/10000000000),((169809100813796107350183427661627026639963991535283927743383:ℚ)/2517959421609765625000000000000000000000000000000000000000000),((-843083900845737682415824637:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((7539678739:ℚ)/10000000000),((4033968271:ℚ)/5000000000),((4:ℚ)/45),((10113968271:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1260756097:ℚ)/10000000000),((976318441006998327169375739195231500245445293779777555359:ℚ)/14363641406250000000000000000000000000000000000000000000000),((-225475063904479789:ℚ)/972800000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((8016906749:ℚ)/10000000000),((9974046323:ℚ)/10000000000),((9:ℚ)/125),((7378015441:ℚ)/43200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3286298827761294516181088372557511900130884380303678763:ℚ)/47239200000000000000000000000000000000000000000000000000),((-239268767:ℚ)/1024000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9923691313:ℚ)/10000000000),((6890602297:ℚ)/5000000000),((6:ℚ)/115),((12970602297:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2662187022998440928977310846683315637611:ℚ)/33856000000000000000000000000000000000000),((-239268767:ℚ)/1024000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
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
private theorem node6_8 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC17
#check @N11Formalization.C450Source20GroupedC17.bound
#print axioms N11Formalization.C450Source20GroupedC17.valid0
#print axioms N11Formalization.C450Source20GroupedC17.valid1
#print axioms N11Formalization.C450Source20GroupedC17.valid2
#print axioms N11Formalization.C450Source20GroupedC17.valid3
#print axioms N11Formalization.C450Source20GroupedC17.valid4
#print axioms N11Formalization.C450Source20GroupedC17.valid5
#print axioms N11Formalization.C450Source20GroupedC17.valid6
#print axioms N11Formalization.C450Source20GroupedC17.valid7
#print axioms N11Formalization.C450Source20GroupedC17.valid8
#print axioms N11Formalization.C450Source20GroupedC17.valid9
#print axioms N11Formalization.C450Source20GroupedC17.valid10
#print axioms N11Formalization.C450Source20GroupedC17.bound
#print axioms N11Formalization.C450Source20GroupedC17.endpoint_checks
