import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/16),((1:ℚ)/2),((5538071589:ℚ)/10000000000),((293411569:ℚ)/500000000),((56686501123:ℚ)/103000000000),((409411569:ℚ)/620000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7543838727:ℚ)/10000000000),((-131845628454530291175696594049481343053262784429370701:ℚ)/509762450000000000000000000000000000000000000000000000),((-2887258667395638476757:ℚ)/7220000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5778632417:ℚ)/10000000000),((3054292539:ℚ)/5000000000),((19456808973:ℚ)/35600000000),((4214292539:ℚ)/6437500000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((883687631:ℚ)/1250000000),((-846203119138173424579087261378743233126046485687563580169:ℚ)/3301807619857788085937500000000000000000000000000000000000),((-861114957158876310096631:ℚ)/2166000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((1504742877:ℚ)/2500000000),((778585727:ℚ)/1250000000),((15013200139:ℚ)/27175000000),((1068585727:ℚ)/1668750000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3283838039:ℚ)/5000000000),((-330650649119472642305998371080522219830715676762758389231:ℚ)/1271010614564514160156250000000000000000000000000000000000),((-18002192671223989177973:ℚ)/45125000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6139065339:ℚ)/10000000000),((3174369689:ℚ)/5000000000),((8699065339:ℚ)/15800000000),((4334369689:ℚ)/6793750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6304339803:ℚ)/10000000000),((-395918044710289984600739122303730511298232110343075241173:ℚ)/1528878231854057312011718750000000000000000000000000000000),((-287052426422306358756277:ℚ)/722000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((6259112239:ℚ)/10000000000),((3234374103:ℚ)/5000000000),((61733785673:ℚ)/112500000000),((627767729:ℚ)/987500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1206248873:ℚ)/2000000000),((-654632473136105246746062604531173813799095762775307:ℚ)/2539072608947753906250000000000000000000000000000000),((-858044007731919681132799:ℚ)/2166000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6379114637:ℚ)/10000000000),((263548583:ℚ)/400000000),((62573802459:ℚ)/114400000000),((39594287:ℚ)/62500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5746967367:ℚ)/10000000000),((-2002717336135479471935386253007228779163095231180133:ℚ)/7800674438476562500000000000000000000000000000000000),((-1823499868074195266293:ℚ)/4620800000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((1624768699:ℚ)/2500000000),((209645019:ℚ)/312500000),((15853380893:ℚ)/29075000000),((21703463:ℚ)/34375000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5449727441:ℚ)/10000000000),((-7981781777836073162561223425877497203326823175246887:ℚ)/31215829658508300781250000000000000000000000000000000),((-1662738410601735317123:ℚ)/4230468750000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1654748707:ℚ)/2500000000),((6828528287:ℚ)/10000000000),((16063240949:ℚ)/29550000000),((9148528287:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5137242363:ℚ)/10000000000),((-142355799501361707916666327189471791965049226895886612992791:ℚ)/558911333526516723632812500000000000000000000000000000000000),((-1130284839549345268258053:ℚ)/2888000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((210589897:ℚ)/312500000),((1413639177:ℚ)/2000000000),((2034129279:ℚ)/3812500000),((1877639177:ℚ)/2955000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((300406623:ℚ)/625000000),((-5526205275877850857270513984394559612746912170545809089:ℚ)/22225338228906250000000000000000000000000000000000000000),((-133479416068629009710719:ℚ)/346560000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((1395706651:ℚ)/2000000000),((3773572509:ℚ)/5000000000),((4451315519:ℚ)/8640000000),((4933572509:ℚ)/7625000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((4072133131:ℚ)/10000000000),((-160102756198651760793803960371642052266095619842280137617:ℚ)/673295690917968750000000000000000000000000000000000000000),((-805350913475335338734791:ℚ)/2166000000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((1864365571:ℚ)/2500000000),((4729577873:ℚ)/5000000000),((17530558997:ℚ)/40000000000),((5889577873:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1939787743:ℚ)/10000000000),((-23544637224836734536693675291422222412789451046953961:ℚ)/123018750000000000000000000000000000000000000000000000),((-722571819140491:ℚ)/1900000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((234235301:ℚ)/250000000),((6636600469:ℚ)/5000000000),((695882369:ℚ)/1840000000),((7796600469:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-126802278619627302410804720030593293327079717295562756031:ℚ)/826562500000000000000000000000000000000000000000000000000),((-1227077:ℚ)/3200000)⟩
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
end N11Formalization.C450Source30GroupedC24
#check @N11Formalization.C450Source30GroupedC24.bound
#print axioms N11Formalization.C450Source30GroupedC24.valid0
#print axioms N11Formalization.C450Source30GroupedC24.valid1
#print axioms N11Formalization.C450Source30GroupedC24.valid2
#print axioms N11Formalization.C450Source30GroupedC24.valid3
#print axioms N11Formalization.C450Source30GroupedC24.valid4
#print axioms N11Formalization.C450Source30GroupedC24.valid5
#print axioms N11Formalization.C450Source30GroupedC24.valid6
#print axioms N11Formalization.C450Source30GroupedC24.valid7
#print axioms N11Formalization.C450Source30GroupedC24.valid8
#print axioms N11Formalization.C450Source30GroupedC24.valid9
#print axioms N11Formalization.C450Source30GroupedC24.valid10
#print axioms N11Formalization.C450Source30GroupedC24.valid11
#print axioms N11Formalization.C450Source30GroupedC24.bound
#print axioms N11Formalization.C450Source30GroupedC24.endpoint_checks
