import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((2995157507:ℚ)/5000000000),((3254822831:ℚ)/5000000000),((23846102549:ℚ)/53400000000),((3654822831:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((414324209:ℚ)/625000000),((963174663753614983115899:ℚ)/356445000000000000000000000),((-284784617669550191329373303:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6466005173:ℚ)/10000000000),((421713489:ℚ)/625000000),((51022036211:ℚ)/110600000000),((471713489:ℚ)/834375000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1106618501:ℚ)/2000000000),((15557270784109220976817951483920479:ℚ)/45871350000000000000000000000000000000),((-1156990441980852358496022663:ℚ)/7393280000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((6703814613:ℚ)/10000000000),((6866294049:ℚ)/10000000000),((17562234097:ℚ)/37500000000),((7666294049:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((981070329:ℚ)/2000000000),((-1238745227985786575184101311451161:ℚ)/1757812500000000000000000000000000000),((-3497939065388169721216105429:ℚ)/22179840000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((170567787:ℚ)/250000000),((6985168009:ℚ)/10000000000),((1337974509:ℚ)/2860000000),((2595056003:ℚ)/4687500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2281088891:ℚ)/5000000000),((-8366200154029796784194657490489:ℚ)/10224500000000000000000000000000000),((-2194669052635899568307029:ℚ)/13862400000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((6941603459:ℚ)/10000000000),((1408920691:ℚ)/2000000000),((54351224213:ℚ)/115350000000),((120686207:ℚ)/220000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4193129513:ℚ)/10000000000),((-3579844234625884277164190763992639:ℚ)/2772004687500000000000000000000000000),((-1175011212144745297391174007:ℚ)/7393280000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((7001047691:ℚ)/10000000000),((888004739:ℚ)/1250000000),((54767333837:ℚ)/116300000000),((329334913:ℚ)/600781250),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((999168359:ℚ)/2500000000),((-4514243999319847722103967471089653:ℚ)/3381422500000000000000000000000000000),((-1177275706650645990502713607:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/16),((1:ℚ)/2),((7060490791:ℚ)/10000000000),((1790867851:ℚ)/2500000000),((55183435537:ℚ)/117250000000),((1990867851:ℚ)/3634375000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3790625521:ℚ)/10000000000),((-35472087858916513494564856182170663:ℚ)/25776679687500000000000000000000000000),((-1179542848549144344832101007:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1423986557:ℚ)/2000000000),((1444580791:ℚ)/2000000000),((11119905899:ℚ)/23640000000),((1604580791:ℚ)/2931250000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1786661403:ℚ)/5000000000),((-494178684314734939726516235516609:ℚ)/349281000000000000000000000000000000),((-47272505547197171936355703:ℚ)/295731200000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((7179373701:ℚ)/10000000000),((3641167793:ℚ)/5000000000),((56015615907:ℚ)/119150000000),((1347055931:ℚ)/2462500000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((835641663:ℚ)/2500000000),((-77259592912652458628809749544065109:ℚ)/53237709375000000000000000000000000000),((-3552255233891716338783615541:ℚ)/22179840000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((7238813563:ℚ)/10000000000),((7341766321:ℚ)/10000000000),((56431694941:ℚ)/120100000000),((8141766321:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((309534509:ℚ)/1000000000),((-6695049193198597888150763178212327:ℚ)/4507503125000000000000000000000000000),((-1186360167173856761944349543:ℚ)/7393280000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((3649126199:ℚ)/5000000000),((7401196179:ℚ)/10000000000),((28423883393:ℚ)/60525000000),((8201196179:ℚ)/15012500000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((70683431:ℚ)/250000000),((-6947319277637634544899226322763373:ℚ)/4579094531250000000000000000000000000),((-297159476800486193604931247:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((7357690229:ℚ)/10000000000),((3730312591:ℚ)/5000000000),((57263831603:ℚ)/122000000000),((4130312591:ℚ)/7565625000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1265972739:ℚ)/5000000000),((-28779781190809189757302081870586143:ℚ)/18605000000000000000000000000000000000),((-1190918298791666867513278727:ℚ)/7393280000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((7417127081:ℚ)/10000000000),((75794807:ℚ)/100000000),((57679889567:ℚ)/123900000000),((83794807:ℚ)/152500000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1099075719:ℚ)/5000000000),((-11812509196165691500953437407836467:ℚ)/9594506250000000000000000000000000000),((-1193201342767554224801840367:ℚ)/7393280000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7535997933:ℚ)/10000000000),((3849166513:ℚ)/5000000000),((58511985531:ℚ)/125800000000),((4249166513:ℚ)/7743750000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1298704819:ℚ)/10000000000),((-795223064829627699481886684255859:ℚ)/618189062500000000000000000000000000),((-3593326171862168824200858949:ℚ)/22179840000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((765486513:ℚ)/1000000000),((7936028667:ℚ)/10000000000),((659378399:ℚ)/1440000000),((8736028667:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-1786185720210892418078375988391:ℚ)/2592000000000000000000000000000000),((-83119293:ℚ)/512000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((19731473:ℚ)/25000000),((4918629471:ℚ)/5000000000),((152520311:ℚ)/400000000),((5318629471:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((911178700624570060571840650427:ℚ)/150000000000000000000000000000000),((-83119293:ℚ)/512000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((2448499549:ℚ)/2500000000),((2727740521:ℚ)/2000000000),((18579496843:ℚ)/55200000000),((2887740521:ℚ)/4000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4807580127883305476485051:ℚ)/380880000000000000000000000),((-83119293:ℚ)/512000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC24
#check @N11Formalization.C450Source11GroupedC24.bound
#print axioms N11Formalization.C450Source11GroupedC24.valid0
#print axioms N11Formalization.C450Source11GroupedC24.valid1
#print axioms N11Formalization.C450Source11GroupedC24.valid2
#print axioms N11Formalization.C450Source11GroupedC24.valid3
#print axioms N11Formalization.C450Source11GroupedC24.valid4
#print axioms N11Formalization.C450Source11GroupedC24.valid5
#print axioms N11Formalization.C450Source11GroupedC24.valid6
#print axioms N11Formalization.C450Source11GroupedC24.valid7
#print axioms N11Formalization.C450Source11GroupedC24.valid8
#print axioms N11Formalization.C450Source11GroupedC24.valid9
#print axioms N11Formalization.C450Source11GroupedC24.valid10
#print axioms N11Formalization.C450Source11GroupedC24.valid11
#print axioms N11Formalization.C450Source11GroupedC24.valid12
#print axioms N11Formalization.C450Source11GroupedC24.valid13
#print axioms N11Formalization.C450Source11GroupedC24.valid14
#print axioms N11Formalization.C450Source11GroupedC24.valid15
#print axioms N11Formalization.C450Source11GroupedC24.valid16
#print axioms N11Formalization.C450Source11GroupedC24.bound
#print axioms N11Formalization.C450Source11GroupedC24.endpoint_checks
