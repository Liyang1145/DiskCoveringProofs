import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/16),((1:ℚ)/2),((1097258367:ℚ)/2000000000),((727677347:ℚ)/1250000000),((11520808569:ℚ)/20600000000),((1037677347:ℚ)/1550000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1910701057:ℚ)/2500000000),((-15219372340845668301065491444375465672864136153598122511:ℚ)/49383237343750000000000000000000000000000000000000000000),((-46059451577094011874109:ℚ)/112812500000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((715912391:ℚ)/1250000000),((3031101753:ℚ)/5000000000),((7411386737:ℚ)/13350000000),((4271101753:ℚ)/6437500000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7172868181:ℚ)/10000000000),((-605216592574909785600402233489326144219965398683074478463:ℚ)/1981084571914672851562500000000000000000000000000000000000),((-2194333781523064043412377:ℚ)/5415000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((2984025841:ℚ)/5000000000),((6182508039:ℚ)/10000000000),((30488180887:ℚ)/54350000000),((97331551:ℚ)/150000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((417290193:ℚ)/625000000),((-514102849326425845581582383641805733488881052132701849:ℚ)/1661581406250000000000000000000000000000000000000000000),((-8797000561914446760402713:ℚ)/21660000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1522085251:ℚ)/2500000000),((1260551629:ℚ)/2000000000),((15454596757:ℚ)/27650000000),((1756551629:ℚ)/2717500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1604174261:ℚ)/2500000000),((-110774462581660635131063277517075409622504801374977056691:ℚ)/359592160132074279785156250000000000000000000000000000000),((-116793229681487692321691:ℚ)/288800000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((6208576441:ℚ)/10000000000),((6422956649:ℚ)/10000000000),((62660035087:ℚ)/112500000000),((8902956649:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((192109217:ℚ)/312500000),((-15266665727389212797759118341101010082876146989115867:ℚ)/49765823135375976562500000000000000000000000000000000),((-2906737156103480158615251:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6328760791:ℚ)/10000000000),((817888273:ℚ)/1250000000),((4884717349:ℚ)/8800000000),((1127888273:ℚ)/1757812500),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1466932697:ℚ)/2500000000),((-128516787381496358390918384747080353302441370601334462117:ℚ)/420613288879394531250000000000000000000000000000000000000),((-45203957013126291189229:ℚ)/112812500000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3224448329:ℚ)/5000000000),((6663209207:ℚ)/10000000000),((32171138303:ℚ)/58150000000),((831200837:ℚ)/1300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5575782341:ℚ)/10000000000),((-1130624330674050417182841073118496963221702267811923269089:ℚ)/3714492616250000000000000000000000000000000000000000000000),((-2878779472367226738465299:ℚ)/7220000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3284493237:ℚ)/5000000000),((6783268009:ℚ)/10000000000),((10863817553:ℚ)/19700000000),((9263268009:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2634795797:ℚ)/5000000000),((-11300257721133593588432183764350273550210925838386188802133:ℚ)/37260755568434448242187500000000000000000000000000000000000),((-2863916249907488666354131:ℚ)/7220000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((6689032509:ℚ)/10000000000),((438953837:ℚ)/625000000),((66023227563:ℚ)/122000000000),((593953837:ℚ)/923437500),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4946480213:ℚ)/10000000000),((-417614274723633606108986463313283141312650004426214879211:ℚ)/1406447184797973632812500000000000000000000000000000000000),((-21984516201094268684413:ℚ)/56406250000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((6929001587:ℚ)/10000000000),((7502803251:ℚ)/10000000000),((67703011109:ℚ)/129600000000),((9982803251:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((4233672501:ℚ)/10000000000),((-2768932485105247556764865211632350991463073418780890364861:ℚ)/9695457949218750000000000000000000000000000000000000000000),((-8121648339113520545795153:ℚ)/21660000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((1481699847:ℚ)/2000000000),((9416610787:ℚ)/10000000000),((14211898929:ℚ)/32000000000),((1321845643:ℚ)/1800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((703007:ℚ)/3125000),((-5162580073566074652545811461309455903255598330248853:ℚ)/21870000000000000000000000000000000000000000000000000),((-579051269999527:ℚ)/1520000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((4661086399:ℚ)/5000000000),((661637391:ℚ)/500000000),((42227604793:ℚ)/110400000000),((785637391:ℚ)/1000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-32508693289855750214147141291334545367046898990415147:ℚ)/165312500000000000000000000000000000000000000000000000),((-6160363:ℚ)/16000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC24
#check @N11Formalization.C450Source32GroupedC24.bound
#print axioms N11Formalization.C450Source32GroupedC24.valid0
#print axioms N11Formalization.C450Source32GroupedC24.valid1
#print axioms N11Formalization.C450Source32GroupedC24.valid2
#print axioms N11Formalization.C450Source32GroupedC24.valid3
#print axioms N11Formalization.C450Source32GroupedC24.valid4
#print axioms N11Formalization.C450Source32GroupedC24.valid5
#print axioms N11Formalization.C450Source32GroupedC24.valid6
#print axioms N11Formalization.C450Source32GroupedC24.valid7
#print axioms N11Formalization.C450Source32GroupedC24.valid8
#print axioms N11Formalization.C450Source32GroupedC24.valid9
#print axioms N11Formalization.C450Source32GroupedC24.valid10
#print axioms N11Formalization.C450Source32GroupedC24.valid11
#print axioms N11Formalization.C450Source32GroupedC24.bound
#print axioms N11Formalization.C450Source32GroupedC24.endpoint_checks
