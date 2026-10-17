import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((598735201:ℚ)/1000000000),((3263820493:ℚ)/5000000000),((1238735201:ℚ)/5340000000),((16511461479:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6635519783:ℚ)/10000000000),((3466049276736340548775654909550319997939:ℚ)/35076469248000000000000000000000000000000),((-548064723045967451772597223:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6466307909:ℚ)/10000000000),((3383389589:ℚ)/5000000000),((1838043987:ℚ)/7900000000),((5623389589:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5532334451:ℚ)/10000000000),((30406272281249579983125199446126525686279721420704680940599:ℚ)/329978364675000000000000000000000000000000000000000000000000),((-580133986657895712547802967:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6705579663:ℚ)/10000000000),((6886306363:ℚ)/10000000000),((13105579663:ℚ)/56250000000),((34098919089:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((980083907:ℚ)/2000000000),((4375767658377082958420122686048172408961200436152056112351:ℚ)/48921794775000000000000000000000000000000000000000000000000),((-125498942630489713252180877:ℚ)/389120000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((273006807:ℚ)/400000000),((7005807487:ℚ)/10000000000),((529006807:ℚ)/2288000000),((11485807487:ℚ)/37500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4554828999:ℚ)/10000000000),((299824038160617078780965244138364694003420597238364720243831:ℚ)/3369891357421875000000000000000000000000000000000000000000000),((-2413745999536419668978296463:ℚ)/7393280000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6944732481:ℚ)/10000000000),((3562641921:ℚ)/5000000000),((13344732481:ℚ)/58150000000),((17407925763:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((418300551:ℚ)/1000000000),((17512636782709776219857901540214383250446233729572710735942851:ℚ)/197759586889150000000000000000000000000000000000000000000000000),((-610728489353355414685630607:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((7064267981:ℚ)/10000000000),((3622368319:ℚ)/5000000000),((4488089327:ℚ)/19700000000),((17587104957:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1888586103:ℚ)/5000000000),((525777766239456832077171723758326358975241481309212124826221:ℚ)/5961720890949511718750000000000000000000000000000000000000000),((-617996047230930254172901647:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((3591888993:ℚ)/5000000000),((3682083503:ℚ)/5000000000),((6791888993:ℚ)/30025000000),((5922083503:ℚ)/19700000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3324857077:ℚ)/10000000000),((9085421814587325714578146345162269448095959378469627018555397:ℚ)/103384628067871875000000000000000000000000000000000000000000000),((-625239268417950468904668143:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7303263719:ℚ)/10000000000),((3741788003:ℚ)/5000000000),((13703263719:ℚ)/61000000000),((17945364009:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((28036049:ℚ)/100000000),((3616577702374704123745062879337843883384193988868721985693:ℚ)/41278023305078125000000000000000000000000000000000000000000),((-632458241440739639881747143:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((742272633:ℚ)/1000000000),((1990254327:ℚ)/2500000000),((1382272633:ℚ)/6480000000),((9330762981:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((432820803:ℚ)/2000000000),((13249330351474389880372284748826328125416623344682570990637:ℚ)/145431869238281250000000000000000000000000000000000000000000),((-33667841704699523:ℚ)/97280000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((1975091527:ℚ)/2500000000),((9868450233:ℚ)/10000000000),((3575091527:ℚ)/20000000000),((14348450233:ℚ)/43200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4791734026878716670422554189951730256335413466001031843:ℚ)/47239200000000000000000000000000000000000000000000000000),((-180747097:ℚ)/512000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9808402177:ℚ)/10000000000),((6838577503:ℚ)/5000000000),((16208402177:ℚ)/110400000000),((27235732509:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((38244202493941625281505682824146274359751:ℚ)/304704000000000000000000000000000000000000),((-180747097:ℚ)/512000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC19
#check @N11Formalization.C450Source22GroupedC19.bound
#print axioms N11Formalization.C450Source22GroupedC19.valid0
#print axioms N11Formalization.C450Source22GroupedC19.valid1
#print axioms N11Formalization.C450Source22GroupedC19.valid2
#print axioms N11Formalization.C450Source22GroupedC19.valid3
#print axioms N11Formalization.C450Source22GroupedC19.valid4
#print axioms N11Formalization.C450Source22GroupedC19.valid5
#print axioms N11Formalization.C450Source22GroupedC19.valid6
#print axioms N11Formalization.C450Source22GroupedC19.valid7
#print axioms N11Formalization.C450Source22GroupedC19.valid8
#print axioms N11Formalization.C450Source22GroupedC19.valid9
#print axioms N11Formalization.C450Source22GroupedC19.valid10
#print axioms N11Formalization.C450Source22GroupedC19.bound
#print axioms N11Formalization.C450Source22GroupedC19.endpoint_checks
