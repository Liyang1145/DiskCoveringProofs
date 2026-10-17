import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((6307870753:ℚ)/10000000000),((661426793:ℚ)/1000000000),((-277426793:ℚ)/2480000000),((-2923612259:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5917191319:ℚ)/10000000000),((120272137020019554084623686588309766515863665768770273946863:ℚ)/635147568750000000000000000000000000000000000000000000000000),((-42631256067908422498474343:ℚ)/295731200000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((3274030709:ℚ)/5000000000),((6734359189:ℚ)/10000000000),((-2894359189:ℚ)/25750000000),((-1822092127:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2662042141:ℚ)/5000000000),((4324219746691025698174508154060858841015193155934295097969:ℚ)/23221684931054687500000000000000000000000000000000000000000),((-11647155351658135503618287:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((3334041231:ℚ)/5000000000),((856800243:ℚ)/1250000000),((-376800243:ℚ)/3278125000),((-2002123693:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((5004238653:ℚ)/10000000000),((46360557996898164088636112526792043203157258803349394335357:ℚ)/249585462337500000000000000000000000000000000000000000000000),((-12143832201624370055592647:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6788057579:ℚ)/10000000000),((6974398791:ℚ)/10000000000),((-1044799597:ℚ)/8900000000),((-4364172737:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4664609897:ℚ)/10000000000),((132413183321912456708880544315343114812628141701149896117633:ℚ)/714428311043750000000000000000000000000000000000000000000000),((-50567435698605293589663407:ℚ)/295731200000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((3453994613:ℚ)/5000000000),((1418870429:ℚ)/2000000000),((-650870429:ℚ)/5435000000),((-2361983839:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2150237459:ℚ)/5000000000),((9962321181192130782866189957261141499855135201424808895779:ℚ)/53855025527050781250000000000000000000000000000000000000000),((-13141243999097317156122863:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((878484961:ℚ)/1250000000),((3607132127:ℚ)/5000000000),((-1687132127:ℚ)/13825000000),((-635454883:ℚ)/14062500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3904943217:ℚ)/10000000000),((20800800731684770292448116444921763014807107471997882777:ℚ)/112635176628828048706054687500000000000000000000000000000),((-852624706907811421972967:ℚ)/4620800000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((7147731089:ℚ)/10000000000),((1833534303:ℚ)/2500000000),((-97059367:ℚ)/781250000),((-5443193267:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1733621039:ℚ)/5000000000),((156871927157803224590015738967481219825586214326418870417:ℚ)/850678400000000000000000000000000000000000000000000000000),((-56576480746883771792901767:ℚ)/295731200000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((1816886353:ℚ)/2500000000),((7453972973:ℚ)/10000000000),((-277997921:ℚ)/2200000000),((-1450659059:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((742181931:ℚ)/2500000000),((311229242672958660447342324868831463258369923080943414249:ℚ)/1689786642285156250000000000000000000000000000000000000000),((-3661906367864245910561543:ℚ)/18483200000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1477464901:ℚ)/2000000000),((1893443341:ℚ)/2500000000),((-933443341:ℚ)/7268750000),((-1232394703:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((592822849:ℚ)/2500000000),((163600201647216992843795696583403221654482313614252441447:ℚ)/889156879900000000000000000000000000000000000000000000000),((-2424402806512135519608527:ℚ)/11829248000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((7507070097:ℚ)/10000000000),((1953318689:ℚ)/2500000000),((-993318689:ℚ)/7387500000),((-6521210291:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((391353733:ℚ)/2500000000),((414987508017853562622253289687495029710739530728537533753183:ℚ)/2235762850000000000000000000000000000000000000000000000000000),((-62635209446578095275499143:ℚ)/295731200000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((7746467139:ℚ)/10000000000),((1658384283:ℚ)/2000000000),((-890384283:ℚ)/6100000000),((-7239401417:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((52213341019902040585647414175892021863438081235030086409839:ℚ)/276632755200000000000000000000000000000000000000000000000000),((-111168749:ℚ)/512000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8224923863:ℚ)/10000000000),((10203014621:ℚ)/10000000000),((-6363014621:ℚ)/32400000000),((-8674771589:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((428751478459438983222508472333589799389483296032787476702621:ℚ)/2073600000000000000000000000000000000000000000000000000000000),((-111168749:ℚ)/512000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10135440721:ℚ)/10000000000),((875999419:ℚ)/625000000),((-635999419:ℚ)/2500000000),((-14406322163:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((11926030133614146467466906403632040402989079381995644181769:ℚ)/50458982400000000000000000000000000000000000000000000000000),((-111168749:ℚ)/512000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC13
#check @N11Formalization.C450Source26GroupedC13.bound
#print axioms N11Formalization.C450Source26GroupedC13.valid0
#print axioms N11Formalization.C450Source26GroupedC13.valid1
#print axioms N11Formalization.C450Source26GroupedC13.valid2
#print axioms N11Formalization.C450Source26GroupedC13.valid3
#print axioms N11Formalization.C450Source26GroupedC13.valid4
#print axioms N11Formalization.C450Source26GroupedC13.valid5
#print axioms N11Formalization.C450Source26GroupedC13.valid6
#print axioms N11Formalization.C450Source26GroupedC13.valid7
#print axioms N11Formalization.C450Source26GroupedC13.valid8
#print axioms N11Formalization.C450Source26GroupedC13.valid9
#print axioms N11Formalization.C450Source26GroupedC13.valid10
#print axioms N11Formalization.C450Source26GroupedC13.valid11
#print axioms N11Formalization.C450Source26GroupedC13.valid12
#print axioms N11Formalization.C450Source26GroupedC13.bound
#print axioms N11Formalization.C450Source26GroupedC13.endpoint_checks
