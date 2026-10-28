import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((80229859:ℚ)/125000000),((3362877379:ℚ)/5000000000),((-6568632137:ℚ)/24800000000),((-43429859:ℚ)/257500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2825595453:ℚ)/5000000000),((1059333477015531951161971116714554987925434557283963:ℚ)/4962090380859375000000000000000000000000000000000000),((-480577318329021003461:ℚ)/18483200000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3328997737:ℚ)/5000000000),((3422770723:ℚ)/5000000000),((-6748312169:ℚ)/25750000000),((-1856997737:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2515915741:ℚ)/5000000000),((19402329390826667476432347155972557399114951013895983779:ℚ)/92886739724218750000000000000000000000000000000000000000),((-1114920230898051170196589:ℚ)/29573120000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((3388870443:ℚ)/5000000000),((3482645391:ℚ)/5000000000),((-6927936173:ℚ)/26225000000),((-1916870443:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1173676003:ℚ)/2500000000),((208071540182723054006751353483542001539491355110938377607:ℚ)/998341849350000000000000000000000000000000000000000000000),((-3867329190047282269418207:ℚ)/88719360000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((137949009:ℚ)/200000000),((1417000951:ℚ)/2000000000),((-2843002853:ℚ)/10680000000),((-79069009:ℚ)/434800000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4333615857:ℚ)/10000000000),((14265322113014276256422818066385719183119366214369007:ℚ)/68585117860200000000000000000000000000000000000000000),((-7027662658254687228983:ℚ)/141950976000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1754281519:ℚ)/2500000000),((893106133:ℚ)/1250000000),((-1799318399:ℚ)/6793750000),((-339427173:ℚ)/1827500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((788389861:ℚ)/2000000000),((1067739849670368022233395191129547217145627836268318951:ℚ)/5183125580041503906250000000000000000000000000000000000),((-409970562915382893457341:ℚ)/7393280000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((3538475861:ℚ)/5000000000),((3602342609:ℚ)/5000000000),((-7287027827:ℚ)/27412500000),((-2066475861:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((186582921:ℚ)/500000000),((4260004739159783951859942794544090645473231322125831639:ℚ)/20695504618359375000000000000000000000000000000000000000),((-1728075487218438053914101:ℚ)/29573120000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((356838477:ℚ)/500000000),((3632256713:ℚ)/5000000000),((-7376770139:ℚ)/27650000000),((-209638477:ℚ)/1115500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3509439279:ℚ)/10000000000),((30837245699989452300521257711284331612418557184812809:ℚ)/149921491509350585937500000000000000000000000000000000),((-54494076874023200059247:ℚ)/887193600000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((1799144933:ℚ)/2500000000),((3662166947:ℚ)/5000000000),((-7466500841:ℚ)/27887500000),((-1063144933:ℚ)/5625000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1636428839:ℚ)/5000000000),((2988852274780935908465402387930445438677831027145432629:ℚ)/14541140198707580566406250000000000000000000000000000000),((-476265923434722586047509:ℚ)/7393280000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((3628191247:ℚ)/5000000000),((744395239:ℚ)/1000000000),((-1529185717:ℚ)/5625000000),((-2156191247:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3018532697:ℚ)/10000000000),((8714259609579012870701603948561455422236666915028094243:ℚ)/42108580800000000000000000000000000000000000000000000000),((-1993859091317907951781629:ℚ)/29573120000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7375966481:ℚ)/10000000000),((1920776187:ℚ)/2500000000),((-363848051:ℚ)/1300000000),((-4431966481:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2434094097:ℚ)/10000000000),((240410167731072438527009846207042668174410548512952981:ℚ)/1146805950000000000000000000000000000000000000000000000),((-8688213976704594319713341:ℚ)/118292480000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((237970413:ℚ)/312500000),((3961076581:ℚ)/5000000000),((-8363229743:ℚ)/29550000000),((-145970413:ℚ)/762500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((171148871375541283518591229619270309155111556355040543:ℚ)/818760809326171875000000000000000000000000000000000000),((-86848027:ℚ)/1024000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((3927020087:ℚ)/5000000000),((8399975173:ℚ)/10000000000),((-18159925519:ℚ)/61000000000),((-818340029:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1095727663818503715027413449178878444133393216152236767:ℚ)/5122828800000000000000000000000000000000000000000000000),((-86848027:ℚ)/1024000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((8331750273:ℚ)/10000000000),((10308564877:ℚ)/10000000000),((-23885694631:ℚ)/64800000000),((-5387750273:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1992948541864047169012050000655101734514367159022818858453:ℚ)/8294400000000000000000000000000000000000000000000000000000),((-86848027:ℚ)/1024000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((5119999999:ℚ)/5000000000),((14118620623:ℚ)/10000000000),((-35315861869:ℚ)/80000000000),((-3647999999:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6919661197347679668422350098917670339044077384593973673:ℚ)/25229491200000000000000000000000000000000000000000000000),((-86848027:ℚ)/1024000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source24 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source24 nn0 nn1 Qcell ((2231:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source24 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC11
#check @N11Formalization.C450Source24GroupedC11.bound
#print axioms N11Formalization.C450Source24GroupedC11.valid0
#print axioms N11Formalization.C450Source24GroupedC11.valid1
#print axioms N11Formalization.C450Source24GroupedC11.valid2
#print axioms N11Formalization.C450Source24GroupedC11.valid3
#print axioms N11Formalization.C450Source24GroupedC11.valid4
#print axioms N11Formalization.C450Source24GroupedC11.valid5
#print axioms N11Formalization.C450Source24GroupedC11.valid6
#print axioms N11Formalization.C450Source24GroupedC11.valid7
#print axioms N11Formalization.C450Source24GroupedC11.valid8
#print axioms N11Formalization.C450Source24GroupedC11.valid9
#print axioms N11Formalization.C450Source24GroupedC11.valid10
#print axioms N11Formalization.C450Source24GroupedC11.valid11
#print axioms N11Formalization.C450Source24GroupedC11.valid12
#print axioms N11Formalization.C450Source24GroupedC11.valid13
#print axioms N11Formalization.C450Source24GroupedC11.bound
#print axioms N11Formalization.C450Source24GroupedC11.endpoint_checks
