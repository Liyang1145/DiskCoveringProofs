import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5779838183:ℚ)/10000000000),((6319040489:ℚ)/10000000000),((20539514549:ℚ)/35600000000),((7343040489:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1413411613:ℚ)/2000000000),((-73967112116424141541507142984915471:ℚ)/5639752000000000000000000000000000000),((-4362067268071867037032263429:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((625627711:ℚ)/1000000000),((6557176391:ℚ)/10000000000),((6590649399:ℚ)/11060000000),((2527058797:ℚ)/3560000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3018908971:ℚ)/5000000000),((-81992581542559275203025653036434231341050656112198223:ℚ)/4227809425000000000000000000000000000000000000000000000),((-4389537570821742619867365669:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6494422109:ℚ)/10000000000),((6795269889:ℚ)/10000000000),((68049798981:ℚ)/114400000000),((7819269889:ℚ)/11060000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1365381353:ℚ)/2500000000),((-92707540352157684698582306338878696085623109479888674333:ℚ)/4678731200000000000000000000000000000000000000000000000000),((-4399624058881761596071010229:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1346504819:ℚ)/2000000000),((6914302041:ℚ)/10000000000),((14038543371:ℚ)/23260000000),((7938302041:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((192982129:ℚ)/400000000),((-220904246180338436520015385715889055432761158054053227:ℚ)/9831485918750000000000000000000000000000000000000000000),((-4413132217990824963826624869:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3425780141:ℚ)/5000000000),((1758331273:ℚ)/2500000000),((11877340423:ℚ)/19700000000),((2014331273:ℚ)/2907500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2237622613:ℚ)/5000000000),((-404280668912069249852432940896679375357530788756263133:ℚ)/17918842968750000000000000000000000000000000000000000000),((-276126046877197355409284421:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6970587237:ℚ)/10000000000),((3576169737:ℚ)/5000000000),((72335285133:ℚ)/120100000000),((4088169737:ℚ)/5910000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((819690327:ℚ)/2000000000),((-122558801331854141523703441578553327263566633205941970069:ℚ)/5413511253125000000000000000000000000000000000000000000000),((-1105709544776765683962227781:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((3544802699:ℚ)/5000000000),((1454269119:ℚ)/2000000000),((36703224291:ℚ)/61000000000),((1659069119:ℚ)/2402000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3685719063:ℚ)/10000000000),((-16103445965759507474196845034162360103901577856276423787:ℚ)/709315625000000000000000000000000000000000000000000000000),((-177103861490755966472398389:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((360430759:ℚ)/500000000),((1847585959:ℚ)/2500000000),((1241292277:ℚ)/2065000000),((2103585959:ℚ)/3050000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((50363029:ℚ)/156250000),((-156523677203476185443007669900094314835558454172421:ℚ)/6879394238281250000000000000000000000000000000000000),((-277018240934492321184640869:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7327616969:ℚ)/10000000000),((1501866911:ℚ)/2000000000),((4444032513:ℚ)/7400000000),((1706666911:ℚ)/2478000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2685368699:ℚ)/10000000000),((-28182281531590976837303165799078195280737701600681:ℚ)/1236645507812500000000000000000000000000000000000000),((-177476966418517033965280629:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((7446611129:ℚ)/10000000000),((7747294759:ℚ)/10000000000),((25539833387:ℚ)/43200000000),((8771294759:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((251563887:ℚ)/1250000000),((-2391495444642494766794311461607308020455949483952377:ℚ)/115200000000000000000000000000000000000000000000000000),((-14613315796564467:ℚ)/48640000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7684577909:ℚ)/10000000000),((1930037547:ℚ)/2000000000),((78761201181:ℚ)/160000000000),((2134837547:ℚ)/2592000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-7653946283801194647290106762446981:ℚ)/24000000000000000000000000000000000000),((-308412543:ℚ)/1024000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((47937561:ℚ)/50000000),((336339517:ℚ)/250000000),((159812683:ℚ)/368000000),((361939517:ℚ)/400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((274458226186696506387:ℚ)/16928000000000000000000),((-308412543:ℚ)/1024000000)⟩
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
end N11Formalization.C450Source17GroupedC26
#check @N11Formalization.C450Source17GroupedC26.bound
#print axioms N11Formalization.C450Source17GroupedC26.valid0
#print axioms N11Formalization.C450Source17GroupedC26.valid1
#print axioms N11Formalization.C450Source17GroupedC26.valid2
#print axioms N11Formalization.C450Source17GroupedC26.valid3
#print axioms N11Formalization.C450Source17GroupedC26.valid4
#print axioms N11Formalization.C450Source17GroupedC26.valid5
#print axioms N11Formalization.C450Source17GroupedC26.valid6
#print axioms N11Formalization.C450Source17GroupedC26.valid7
#print axioms N11Formalization.C450Source17GroupedC26.valid8
#print axioms N11Formalization.C450Source17GroupedC26.valid9
#print axioms N11Formalization.C450Source17GroupedC26.valid10
#print axioms N11Formalization.C450Source17GroupedC26.valid11
#print axioms N11Formalization.C450Source17GroupedC26.bound
#print axioms N11Formalization.C450Source17GroupedC26.endpoint_checks
