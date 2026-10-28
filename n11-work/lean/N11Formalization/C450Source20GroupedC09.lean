import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((64811029:ℚ)/100000000),((423985313:ℚ)/625000000),((-333985313:ℚ)/775000000),((-332077203:ℚ)/1030000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((549517351:ℚ)/1000000000),((8514545350919246778338207917950290947766387625966483:ℚ)/105857928125000000000000000000000000000000000000000000),((267725659553699348002003:ℚ)/1478656000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6719859969:ℚ)/10000000000),((1725782291:ℚ)/2500000000),((-1365782291:ℚ)/3218750000),((-34879019783:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((121508669:ℚ)/250000000),((7237559097208448982491242625736603266024664411595142848911:ℚ)/92886739724218750000000000000000000000000000000000000000000),((7808031972918286262548765889:ℚ)/44359680000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((1709801023:ℚ)/2500000000),((1404494261:ℚ)/2000000000),((-1116494261:ℚ)/2622500000),((-2976202387:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((180506803:ℚ)/400000000),((44973772286433020710233026916774746997113437286790685013:ℚ)/577744125781250000000000000000000000000000000000000000000),((160321225269178617995257707:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((3479263461:ℚ)/5000000000),((3541067243:ℚ)/5000000000),((-2821067243:ℚ)/6675000000),((-18274844227:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2069047773:ℚ)/5000000000),((13030220530942853007784454086703983840596213569120384373:ℚ)/169887690520286560058593750000000000000000000000000000000),((1895577079090131673467474329:ℚ)/11089920000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1754545177:ℚ)/2500000000),((1428358519:ℚ)/2000000000),((-1140358519:ℚ)/2693750000),((-9241816239:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3938334613:ℚ)/10000000000),((2072597947273417278864130578820144027067578754923363617631:ℚ)/27029371669580078125000000000000000000000000000000000000000),((434300918428983258342787:ℚ)/2560000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7077829587:ℚ)/10000000000),((7201445763:ℚ)/10000000000),((-5761445763:ℚ)/13587500000),((-37384807109:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((466061093:ℚ)/1250000000),((28608449128729337345602113843196003727357411924215836155759:ℚ)/373185041762988281250000000000000000000000000000000000000000),((7468699683608482557050663081:ℚ)/44359680000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7137473689:ℚ)/10000000000),((181527353:ℚ)/250000000),((-145527353:ℚ)/342656250),((-37802315823:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((219171453:ℚ)/625000000),((11102906279762675572387683891186310345867007784048000717881:ℚ)/144868532328515625000000000000000000000000000000000000000000),((2470569443707697236516858043:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((449819571:ℚ)/625000000),((7320737789:ℚ)/10000000000),((-5880737789:ℚ)/13825000000),((-2388736997:ℚ)/6971875000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3270673759:ℚ)/10000000000),((2804532554029901300803884737733650944904343088762818059:ℚ)/36601926638025045394897460937500000000000000000000000000),((28728875668637755950840809:ℚ)/173280000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((7256748049:ℚ)/10000000000),((738037689:ℚ)/1000000000),((-594037689:ℚ)/1394375000),((-12879078781:ℚ)/37500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3016914351:ℚ)/10000000000),((330047467039041323509749594079239357980618651767624956287:ℚ)/4308485984802246093750000000000000000000000000000000000000),((2432450372581321980246321483:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((1463275709:ℚ)/2000000000),((7499641847:ℚ)/10000000000),((-6059641847:ℚ)/14062500000),((-7810929963:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((548109943:ℚ)/2000000000),((26132690030731473971193451996349649075439726228923247517:ℚ)/336868646400000000000000000000000000000000000000000000000),((267404804714070696871243:ℚ)/1638400000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3717813363:ℚ)/5000000000),((7738121791:ℚ)/10000000000),((-484470907:ℚ)/1100000000),((-19944693541:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2083577567:ℚ)/10000000000),((15650892637894940535539841932249732589990643447764528041:ℚ)/197107272656250000000000000000000000000000000000000000000),((1781219446634797490560203881:ℚ)/11089920000000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((7674074753:ℚ)/10000000000),((7976540333:ℚ)/10000000000),((-6536540333:ℚ)/14775000000),((-41558523271:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((265586556068224999904260818408017467903472514955217474875639:ℚ)/3353644275000000000000000000000000000000000000000000000000000),((160788673:ℚ)/1024000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((791246339:ℚ)/1000000000),((338128599:ℚ)/400000000),((-280528599:ℚ)/610000000),((-4322724373:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((11383841917250588621660458418442898201294465421555792221:ℚ)/138316377600000000000000000000000000000000000000000000000),((160788673:ℚ)/1024000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8389083537:ℚ)/10000000000),((5179158247:ℚ)/5000000000),((-4459158247:ℚ)/8100000000),((-46563584759:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((101328282243325022335213499561298536388908396535100689634481:ℚ)/1036800000000000000000000000000000000000000000000000000000000),((160788673:ℚ)/1024000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((5147009619:ℚ)/5000000000),((7082147707:ℚ)/5000000000),((-6362147707:ℚ)/10000000000),((-29949067333:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((358183940088458473475007259040617700033234328831212499529:ℚ)/3153686400000000000000000000000000000000000000000000000000),((160788673:ℚ)/1024000000)⟩
theorem valid14 : Valid source20 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC09
#check @N11Formalization.C450Source20GroupedC09.bound
#print axioms N11Formalization.C450Source20GroupedC09.valid0
#print axioms N11Formalization.C450Source20GroupedC09.valid1
#print axioms N11Formalization.C450Source20GroupedC09.valid2
#print axioms N11Formalization.C450Source20GroupedC09.valid3
#print axioms N11Formalization.C450Source20GroupedC09.valid4
#print axioms N11Formalization.C450Source20GroupedC09.valid5
#print axioms N11Formalization.C450Source20GroupedC09.valid6
#print axioms N11Formalization.C450Source20GroupedC09.valid7
#print axioms N11Formalization.C450Source20GroupedC09.valid8
#print axioms N11Formalization.C450Source20GroupedC09.valid9
#print axioms N11Formalization.C450Source20GroupedC09.valid10
#print axioms N11Formalization.C450Source20GroupedC09.valid11
#print axioms N11Formalization.C450Source20GroupedC09.valid12
#print axioms N11Formalization.C450Source20GroupedC09.valid13
#print axioms N11Formalization.C450Source20GroupedC09.valid14
#print axioms N11Formalization.C450Source20GroupedC09.bound
#print axioms N11Formalization.C450Source20GroupedC09.endpoint_checks
