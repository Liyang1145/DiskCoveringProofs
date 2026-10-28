import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5705531503:ℚ)/10000000000),((6248264317:ℚ)/10000000000),((72360846533:ℚ)/106800000000),((21304792951:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((360816593:ℚ)/500000000),((-6021521700713770790592703480095614623:ℚ)/152273304000000000000000000000000000000),((-4593139453084863267744772959:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1545390813:ℚ)/2500000000),((6486254419:ℚ)/10000000000),((19399298943:ℚ)/27650000000),((22018763257:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((310442789:ℚ)/500000000),((-3151561288994844695951945994304845683437368104077612839:ℚ)/66059522265625000000000000000000000000000000000000000000),((-4578116639801512115614462591:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((1604881449:ℚ)/2500000000),((1681052967:ℚ)/2500000000),((20053695939:ℚ)/28600000000),((811879843:ℚ)/987500000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((141209911:ℚ)/250000000),((-3508060268470581563788965121253187126178471151181530747:ℚ)/73105175000000000000000000000000000000000000000000000000),((-855543732514844160597552677:ℚ)/2772480000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((832182191:ℚ)/1250000000),((6843179351:ℚ)/10000000000),((10354004101:ℚ)/14537500000),((23089538053:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((251664957:ℚ)/500000000),((-371246168422898766549118019763039118379791829105611471:ℚ)/7200795350646972656250000000000000000000000000000000000),((-4555218780524785081760593431:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((3388206393:ℚ)/5000000000),((435133739:ℚ)/625000000),((14023423441:ℚ)/19700000000),((1465401217:ℚ)/1817187500),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2349282577:ℚ)/5000000000),((-924299952932240874843841982680304965134963878574101179:ℚ)/17918842968750000000000000000000000000000000000000000000),((-17763629408649747301003951:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6895361429:ℚ)/10000000000),((7081093621:ℚ)/10000000000),((85448975719:ℚ)/120100000000),((23803280863:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((434015697:ℚ)/1000000000),((-838033297401896855302646772886397160766468810497962622949:ℚ)/16240533759375000000000000000000000000000000000000000000000),((-4539710937764226885951945071:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((1753575943:ℚ)/2500000000),((7200041053:ℚ)/10000000000),((21689335373:ℚ)/30500000000),((24160123159:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1975803591:ℚ)/5000000000),((-4576233528167731298263101038377873079929281981347779749:ℚ)/88664453125000000000000000000000000000000000000000000000),((-4531884195691846706176798879:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((7133240109:ℚ)/10000000000),((457436401:ℚ)/625000000),((29355213733:ℚ)/41300000000),((25119823:ℚ)/31250000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1761461443:ℚ)/5000000000),((-2840789096686014634355746263331017780972876396423554069:ℚ)/55035153906250000000000000000000000000000000000000000000),((-17671909728899617087113031:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((7252170719:ℚ)/10000000000),((1487583597:ℚ)/2000000000),((89373877909:ℚ)/125800000000),((4974750791:ℚ)/6195000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((607423663:ℚ)/2000000000),((-313600029117790388032997713453505034750569202290180917:ℚ)/6075639379882812500000000000000000000000000000000000000),((-541930201392039985117149437:ℚ)/1774387200000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((368554793:ℚ)/500000000),((7675772763:ℚ)/10000000000),((4534102723:ℚ)/6480000000),((25587318289:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((307568001:ℚ)/1250000000),((-1531647510039029580428157057252952510405753307903393:ℚ)/31492800000000000000000000000000000000000000000000000),((-311994997:ℚ)/1024000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((3804465353:ℚ)/5000000000),((4789001653:ℚ)/5000000000),((46649118883:ℚ)/80000000000),((15647004959:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-5752691933505329152883246821469965931070970201415677393:ℚ)/300000000000000000000000000000000000000000000000000000000),((-311994997:ℚ)/1024000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((475551799:ℚ)/500000000),((13380619891:ℚ)/10000000000),((5711069789:ℚ)/11040000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((17188881138853971391771946219849:ℚ)/168196608000000000000000000000000000),((-311994997:ℚ)/1024000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC28
#check @N11Formalization.C450Source17GroupedC28.bound
#print axioms N11Formalization.C450Source17GroupedC28.valid0
#print axioms N11Formalization.C450Source17GroupedC28.valid1
#print axioms N11Formalization.C450Source17GroupedC28.valid2
#print axioms N11Formalization.C450Source17GroupedC28.valid3
#print axioms N11Formalization.C450Source17GroupedC28.valid4
#print axioms N11Formalization.C450Source17GroupedC28.valid5
#print axioms N11Formalization.C450Source17GroupedC28.valid6
#print axioms N11Formalization.C450Source17GroupedC28.valid7
#print axioms N11Formalization.C450Source17GroupedC28.valid8
#print axioms N11Formalization.C450Source17GroupedC28.valid9
#print axioms N11Formalization.C450Source17GroupedC28.valid10
#print axioms N11Formalization.C450Source17GroupedC28.valid11
#print axioms N11Formalization.C450Source17GroupedC28.bound
#print axioms N11Formalization.C450Source17GroupedC28.endpoint_checks
