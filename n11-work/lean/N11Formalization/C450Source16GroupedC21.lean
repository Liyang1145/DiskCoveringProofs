import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((299312367:ℚ)/500000000),((6512941081:ℚ)/10000000000),((411312367:ℚ)/1335000000),((8432941081:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((829734917:ℚ)/1250000000),((55301479574554819889199866896747756771:ℚ)/1739792874700800000000000000000000000000),((-1665472156361639214704207:ℚ)/8192000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6463122619:ℚ)/10000000000),((6751201367:ℚ)/10000000000),((8703122619:ℚ)/27650000000),((8671201367:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5540305789:ℚ)/10000000000),((19833092844869845706170511232457015855037400919810729839877:ℚ)/698498202344040000000000000000000000000000000000000000000000),((-32766403815167178011784317:ℚ)/155648000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((6701463091:ℚ)/10000000000),((6870312161:ℚ)/10000000000),((993495899:ℚ)/3125000000),((8790312161:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1227978869:ℚ)/2500000000),((3256252897843724150595705454586810985972363511471279:ℚ)/120794555000000000000000000000000000000000000000000000),((-33326858314597693870284013:ℚ)/155648000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((6820611927:ℚ)/10000000000),((3494705459:ℚ)/5000000000),((9060611927:ℚ)/28600000000),((4454705459:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4568444427:ℚ)/10000000000),((60779246927621408353217292840870161093673726476354342483:ℚ)/2274676666259765625000000000000000000000000000000000000000),((-8399153222884704784746293:ℚ)/38912000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((138794949:ℚ)/200000000),((7108498231:ℚ)/10000000000),((183594949:ℚ)/581500000),((9028498231:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((419912381:ℚ)/1000000000),((1935545517184541699944523610300061458077166468861656935793:ℚ)/73018924389840000000000000000000000000000000000000000000000),((-33865984894170457950822333:ℚ)/155648000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/4),((5:ℚ)/16),((7058870317:ℚ)/10000000000),((716803777:ℚ)/1000000000),((9298870317:ℚ)/29312500000),((908803777:ℚ)/2326000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((759276659:ℚ)/2000000000),((4202682675960529113100962253944196953358727776756970987:ℚ)/162190760563062656250000000000000000000000000000000000000),((-341456153051704735595437:ℚ)/1556480000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3559213599:ℚ)/5000000000),((3613787327:ℚ)/5000000000),((4679213599:ℚ)/14775000000),((4573787327:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3578982239:ℚ)/10000000000),((284032451049071061838330070035888492395430051689460460759:ℚ)/10996223413460998535156250000000000000000000000000000000000),((-8570013990762608346213037:ℚ)/38912000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((7177981143:ℚ)/10000000000),((7346640709:ℚ)/10000000000),((9417981143:ℚ)/30025000000),((9266640709:ℚ)/23640000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3348147347:ℚ)/10000000000),((116794953908857292024544150667413936326104260581683774253519:ℚ)/4466215932532065000000000000000000000000000000000000000000000),((-34403587483639457393112293:ℚ)/155648000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((7297080501:ℚ)/10000000000),((93321211:ℚ)/125000000),((9537080501:ℚ)/30500000000),((117321211:ℚ)/300250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((22662873:ℚ)/80000000),((204617344170833165941008005258460956109994254051247:ℚ)/7868623192530517578125000000000000000000000000000000),((-5417472026256581008813:ℚ)/24320000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((7416168931:ℚ)/10000000000),((7703781377:ℚ)/10000000000),((9656168931:ℚ)/31450000000),((9623781377:ℚ)/24400000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2203925807:ℚ)/10000000000),((2988098233879151958860184107073415481319001404471064750361:ℚ)/112253737276250000000000000000000000000000000000000000000000),((-43671002367036759:ℚ)/194560000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((3827157499:ℚ)/5000000000),((3970915739:ℚ)/5000000000),((4947157499:ℚ)/16200000000),((290053867:ℚ)/740000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5482039033819263924884319000098176557805656161746219:ℚ)/207708958125000000000000000000000000000000000000000000),((-46558701:ℚ)/204800000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((986552879:ℚ)/1250000000),((4922644591:ℚ)/5000000000),((1266552879:ℚ)/5000000000),((5882644591:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1077094003631625428230958943475100668156161241598069:ℚ)/31886460000000000000000000000000000000000000000000000),((-46558701:ℚ)/204800000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((4898122299:ℚ)/5000000000),((6824671857:ℚ)/5000000000),((6018122299:ℚ)/27600000000),((7784671857:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2705266267085168654744412085796741467:ℚ)/60940800000000000000000000000000000000),((-46558701:ℚ)/204800000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source16 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC21
#check @N11Formalization.C450Source16GroupedC21.bound
#print axioms N11Formalization.C450Source16GroupedC21.valid0
#print axioms N11Formalization.C450Source16GroupedC21.valid1
#print axioms N11Formalization.C450Source16GroupedC21.valid2
#print axioms N11Formalization.C450Source16GroupedC21.valid3
#print axioms N11Formalization.C450Source16GroupedC21.valid4
#print axioms N11Formalization.C450Source16GroupedC21.valid5
#print axioms N11Formalization.C450Source16GroupedC21.valid6
#print axioms N11Formalization.C450Source16GroupedC21.valid7
#print axioms N11Formalization.C450Source16GroupedC21.valid8
#print axioms N11Formalization.C450Source16GroupedC21.valid9
#print axioms N11Formalization.C450Source16GroupedC21.valid10
#print axioms N11Formalization.C450Source16GroupedC21.valid11
#print axioms N11Formalization.C450Source16GroupedC21.valid12
#print axioms N11Formalization.C450Source16GroupedC21.bound
#print axioms N11Formalization.C450Source16GroupedC21.endpoint_checks
