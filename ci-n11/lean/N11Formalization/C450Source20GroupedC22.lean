import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((5874839687:ℚ)/10000000000),((25058079:ℚ)/39062500),((8178839687:ℚ)/21360000000),((98924237:ℚ)/193750000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1374463279:ℚ)/2000000000),((2116236548263464537308219:ℚ)/57031200000000000000000000),((-553046739182102961121939:ℚ)/1805000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1588178553:ℚ)/2500000000),((3326790671:ℚ)/5000000000),((2164178553:ℚ)/5530000000),((13020372013:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5810560393:ℚ)/10000000000),((1746359650939978798306132124272952255188610368238466689097551:ℚ)/54570172058128125000000000000000000000000000000000000000000000),((-146017128839337655431328751:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((3295751053:ℚ)/5000000000),((6892213291:ℚ)/10000000000),((4447751053:ℚ)/11440000000),((26756639873:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2605190423:ℚ)/5000000000),((3713776204600914677725088400146199720617542782925360005963:ℚ)/118756146884375000000000000000000000000000000000000000000000),((-591752551137970361230477591:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((6830203789:ℚ)/10000000000),((7011501337:ℚ)/10000000000),((9134203789:ℚ)/23260000000),((27114504011:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((283734347:ℚ)/625000000),((17369314374220092540346168685792520735362804708578553751383713:ℚ)/593278760667450000000000000000000000000000000000000000000000000),((-600547141867313091560568159:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6949524969:ℚ)/10000000000),((7130771971:ℚ)/10000000000),((3084508323:ℚ)/7880000000),((27472315913:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2083727237:ℚ)/5000000000),((519813358933199054704827665425519496042821301963704580724979:ℚ)/17885162672848535156250000000000000000000000000000000000000000),((-604336194713977750726529351:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((7068827657:ℚ)/10000000000),((7250026027:ℚ)/10000000000),((9372827657:ℚ)/24020000000),((27830078081:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((940217717:ℚ)/2500000000),((80618003694707601147442168155669145852709897219700366684222427:ℚ)/2791384957832540625000000000000000000000000000000000000000000000),((-608104505334272735943792919:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((359405637:ℚ)/500000000),((1473852857:ℚ)/2000000000),((474605637:ℚ)/1220000000),((5637558571:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1653668973:ℚ)/5000000000),((578657883444333576223292004841360212848806304598635593939:ℚ)/20143675372878125000000000000000000000000000000000000000000),((-1288109707431809499475781:ℚ)/3891200000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((7307381047:ℚ)/10000000000),((3803848149:ℚ)/5000000000),((9611381047:ℚ)/25160000000),((14451544447:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1391979457:ℚ)/5000000000),((262240918881037043473446203231841593518276217542235100654407:ℚ)/8769823224707031250000000000000000000000000000000000000000000),((-80840524245883953:ℚ)/243200000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((7545870399:ℚ)/10000000000),((7846073351:ℚ)/10000000000),((3283290133:ℚ)/8640000000),((29618220053:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1194218289:ℚ)/10000000000),((16824436591543641221698979433247511333076649068154530365453:ℚ)/566930061815625000000000000000000000000000000000000000000000),((-82151022996634601:ℚ)/243200000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((486518837:ℚ)/625000000),((9751583837:ℚ)/10000000000),((630518837:ℚ)/2000000000),((35334751511:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((159176240686475627419130876217547:ℚ)/3750000000000000000000000000000000),((-43393929:ℚ)/128000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((2422537593:ℚ)/2500000000),((13558041213:ℚ)/10000000000),((999512531:ℚ)/3680000000),((46754123639:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((101237875693727845218211:ℚ)/1692800000000000000000000),((-43393929:ℚ)/128000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC22
#check @N11Formalization.C450Source20GroupedC22.bound
#print axioms N11Formalization.C450Source20GroupedC22.valid0
#print axioms N11Formalization.C450Source20GroupedC22.valid1
#print axioms N11Formalization.C450Source20GroupedC22.valid2
#print axioms N11Formalization.C450Source20GroupedC22.valid3
#print axioms N11Formalization.C450Source20GroupedC22.valid4
#print axioms N11Formalization.C450Source20GroupedC22.valid5
#print axioms N11Formalization.C450Source20GroupedC22.valid6
#print axioms N11Formalization.C450Source20GroupedC22.valid7
#print axioms N11Formalization.C450Source20GroupedC22.valid8
#print axioms N11Formalization.C450Source20GroupedC22.valid9
#print axioms N11Formalization.C450Source20GroupedC22.valid10
#print axioms N11Formalization.C450Source20GroupedC22.bound
#print axioms N11Formalization.C450Source20GroupedC22.endpoint_checks
