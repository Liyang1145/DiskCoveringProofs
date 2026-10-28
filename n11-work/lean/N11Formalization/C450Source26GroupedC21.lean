import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((5814298203:ℚ)/10000000000),((796245509:ℚ)/1250000000),((3218099401:ℚ)/8900000000),((1196245509:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6996940699:ℚ)/10000000000),((1411913588630707580776675521177216257:ℚ)/30204737408000000000000000000000000000),((-357062262847181962399979:ℚ)/924160000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((314728149:ℚ)/500000000),((6609719431:ℚ)/10000000000),((506728149:ℚ)/1382500000),((3269906477:ℚ)/7120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((743563827:ℚ)/1250000000),((74209086766794563313600451671026159467533915319745247618809:ℚ)/2069624303241600000000000000000000000000000000000000000000000),((-23861928696943549148562099:ℚ)/59146240000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((261376797:ℚ)/400000000),((1345907839:ℚ)/2000000000),((46108533:ℚ)/125000000),((1985907839:ℚ)/4424000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((33495871:ℚ)/62500000),((2412559907101138543551039953419987260220444671028327:ℚ)/77308515200000000000000000000000000000000000000000000),((-974538020229539617557539:ℚ)/2365849600000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((3327143919:ℚ)/5000000000),((85616537:ℚ)/125000000),((5247143919:ℚ)/14300000000),((13957393:ℚ)/31250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5041938961:ℚ)/10000000000),((120824985319677113666609227836822145706108244472743:ℚ)/3900337219238281250000000000000000000000000000000000),((-3837534019495093659571:ℚ)/9241600000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((1693529527:ℚ)/2500000000),((174226813:ℚ)/250000000),((2653529527:ℚ)/7268750000),((254226813:ℚ)/572000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((470522949:ℚ)/1000000000),((1107845024096007161124503900302303235107773567583124417:ℚ)/35956288525300000000000000000000000000000000000000000000),((-15471908465069831302971:ℚ)/36966400000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1378782523:ℚ)/2000000000),((7088789551:ℚ)/10000000000),((2146782523:ℚ)/5910000000),((10288789551:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((217234403:ℚ)/500000000),((70286531011734148930262384429534551840876366930191093950867:ℚ)/2289300822124612500000000000000000000000000000000000000000000),((-24947962762928011126502659:ℚ)/59146240000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((876709139:ℚ)/1250000000),((7208475623:ℚ)/10000000000),((1356709139:ℚ)/3753125000),((10408475623:ℚ)/23640000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((790752447:ℚ)/2000000000),((10950830255998621370244444522287772203408767951179037672279819:ℚ)/357297274602565200000000000000000000000000000000000000000000000),((-25138949854323460318647411:ℚ)/59146240000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((178335031:ℚ)/250000000),((7328132203:ℚ)/10000000000),((274335031:ℚ)/762500000),((10528132203:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((352230839:ℚ)/1000000000),((9878084444729107215781955961509049134230933188831553214613:ℚ)/322298805966050000000000000000000000000000000000000000000000),((-25328019008679884644013131:ℚ)/59146240000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((906637317:ℚ)/1250000000),((24395281:ℚ)/31250000),((154070813:ℚ)/450000000),((34395281:ℚ)/76250000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3033033547:ℚ)/10000000000),((2262772633553031389979785570783513212694099212999:ℚ)/56107974243164062500000000000000000000000000000000),((-6518836835655041:ℚ)/15200000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((1932901731:ℚ)/2500000000),((1943341257:ℚ)/2000000000),((2892901731:ℚ)/10000000000),((2583341257:ℚ)/5184000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((11093514012089125102131728443568731256740955735908549:ℚ)/163258675200000000000000000000000000000000000000000000),((-227162981:ℚ)/512000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((964228057:ℚ)/1000000000),((3382165017:ℚ)/2500000000),((1348228057:ℚ)/5520000000),((4182165017:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1715081926628467430846159:ℚ)/15235200000000000000000000),((-227162981:ℚ)/512000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC21
#check @N11Formalization.C450Source26GroupedC21.bound
#print axioms N11Formalization.C450Source26GroupedC21.valid0
#print axioms N11Formalization.C450Source26GroupedC21.valid1
#print axioms N11Formalization.C450Source26GroupedC21.valid2
#print axioms N11Formalization.C450Source26GroupedC21.valid3
#print axioms N11Formalization.C450Source26GroupedC21.valid4
#print axioms N11Formalization.C450Source26GroupedC21.valid5
#print axioms N11Formalization.C450Source26GroupedC21.valid6
#print axioms N11Formalization.C450Source26GroupedC21.valid7
#print axioms N11Formalization.C450Source26GroupedC21.valid8
#print axioms N11Formalization.C450Source26GroupedC21.valid9
#print axioms N11Formalization.C450Source26GroupedC21.valid10
#print axioms N11Formalization.C450Source26GroupedC21.bound
#print axioms N11Formalization.C450Source26GroupedC21.endpoint_checks
