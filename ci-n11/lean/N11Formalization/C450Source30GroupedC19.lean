import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/8),((3:ℚ)/16),((2938449789:ℚ)/5000000000),((775108493:ℚ)/1250000000),((7418449789:ℚ)/25750000000),((149849209:ℚ)/400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6868042923:ℚ)/10000000000),((-13454973638406457762726800597375545708159529119338744319:ℚ)/106711621093750000000000000000000000000000000000000000000),((-13972908510198102158163937:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((6118359253:ℚ)/10000000000),((25163499:ℚ)/39062500),((5026119751:ℚ)/17800000000),((147990497:ℚ)/402343750),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6350411779:ℚ)/10000000000),((-1077783568826994667269328468297918526892732062105741381:ℚ)/8812112500000000000000000000000000000000000000000000000),((-222371473542987382057533:ℚ)/722000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6359530577:ℚ)/10000000000),((6562256269:ℚ)/10000000000),((15319530577:ℚ)/54350000000),((38246768807:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5794200441:ℚ)/10000000000),((-122369139040601367158334895000532589523625521451074239323:ℚ)/1003410549218750000000000000000000000000000000000000000000),((-933623628592162236762071393:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1296003569:ℚ)/2000000000),((6682598939:ℚ)/10000000000),((441143367:ℚ)/1580000000),((38607796817:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5497906521:ℚ)/10000000000),((-46312829001367791577337471194135812368170031024757:ℚ)/385186718750000000000000000000000000000000000000000),((-941579663335970992862093073:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((825055519:ℚ)/1250000000),((6802886763:ℚ)/10000000000),((1945055519:ℚ)/7031250000),((38968660289:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5186695339:ℚ)/10000000000),((-12425276192046632767407047556882658290700607390629:ℚ)/104773789644241333007812500000000000000000000000000),((-949409033983881556498560497:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((268832507:ℚ)/400000000),((6923122541:ℚ)/10000000000),((57021137:ℚ)/208000000),((39329367623:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4857662503:ℚ)/10000000000),((-6581503501122114787968509226516183425446549974643:ℚ)/56243200000000000000000000000000000000000000000000),((-957112131343041751963627553:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6841126369:ℚ)/10000000000),((7043308889:ℚ)/10000000000),((15801126369:ℚ)/58150000000),((39689926667:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4506866837:ℚ)/10000000000),((-141956877984612411788616804959669697336775946083548206691:ℚ)/1228935739843750000000000000000000000000000000000000000000),((-964689318653105772312864873:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((696138799:ℚ)/1000000000),((3581724123:ℚ)/5000000000),((530712933:ℚ)/1970000000),((20025172369:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2064361647:ℚ)/5000000000),((-1362640357782276622457975334829170824472731812159407:ℚ)/11945895312500000000000000000000000000000000000000000),((-243035233728212980485784977:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7081600113:ℚ)/10000000000),((925449371:ℚ)/1250000000),((16041600113:ℚ)/61000000000),((5096348113:ℚ)/14775000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3714845329:ℚ)/10000000000),((-156285780407336385620301505154189701056694761885671271787:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-15187768444625042588926033:ℚ)/46208000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((3660942667:ℚ)/5000000000),((3941707867:ℚ)/5000000000),((8140942667:ℚ)/32400000000),((21105123601:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1356823979:ℚ)/5000000000),((-90318611130687771057344694842419738508838149373187451:ℚ)/874800000000000000000000000000000000000000000000000000),((-4280054339240807:ℚ)/12800000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((312078319:ℚ)/400000000),((391922729:ℚ)/400000000),((670478319:ℚ)/3200000000),((1918168187:ℚ)/5184000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-16404456750968489316841554453482057549952555105906669:ℚ)/204800000000000000000000000000000000000000000000000000),((-70829211:ℚ)/204800000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((1943474647:ℚ)/2000000000),((2723037623:ℚ)/2000000000),((3735474647:ℚ)/22080000000),((11881112869:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-34752737795268988589090452318947381670300283385361879:ℚ)/622950400000000000000000000000000000000000000000000000),((-70829211:ℚ)/204800000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC19
#check @N11Formalization.C450Source30GroupedC19.bound
#print axioms N11Formalization.C450Source30GroupedC19.valid0
#print axioms N11Formalization.C450Source30GroupedC19.valid1
#print axioms N11Formalization.C450Source30GroupedC19.valid2
#print axioms N11Formalization.C450Source30GroupedC19.valid3
#print axioms N11Formalization.C450Source30GroupedC19.valid4
#print axioms N11Formalization.C450Source30GroupedC19.valid5
#print axioms N11Formalization.C450Source30GroupedC19.valid6
#print axioms N11Formalization.C450Source30GroupedC19.valid7
#print axioms N11Formalization.C450Source30GroupedC19.valid8
#print axioms N11Formalization.C450Source30GroupedC19.valid9
#print axioms N11Formalization.C450Source30GroupedC19.valid10
#print axioms N11Formalization.C450Source30GroupedC19.valid11
#print axioms N11Formalization.C450Source30GroupedC19.bound
#print axioms N11Formalization.C450Source30GroupedC19.endpoint_checks
