import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((384808033:ℚ)/625000000),((1332600841:ℚ)/2000000000),((16:ℚ)/267),((2740600841:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3132179227:ℚ)/5000000000),((27541695572005216281788575515328223091:ℚ)/966551597056000000000000000000000000000),((-3822220075758301:ℚ)/60800000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((6633039109:ℚ)/10000000000),((6781964251:ℚ)/10000000000),((64:ℚ)/1087),((4607321417:ℚ)/35600000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1274878133:ℚ)/2500000000),((570789391751731889278681161179070495187037260680001023257761:ℚ)/20824237909025000000000000000000000000000000000000000000000000),((-65884630962757873:ℚ)/972800000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6752042409:ℚ)/10000000000),((6900917061:ℚ)/10000000000),((32:ℚ)/553),((13940917061:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((953780573:ℚ)/2000000000),((37325972861758137011116748229363242931672999454516549005739:ℚ)/1369874895741235351562500000000000000000000000000000000000000),((-67066666583987973:ℚ)/972800000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((343551849:ℚ)/500000000),((1754965751:ℚ)/2500000000),((64:ℚ)/1125),((3514965751:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((883130689:ℚ)/2000000000),((863118885021819689273510471189061518446805193346810667:ℚ)/31850126806640625000000000000000000000000000000000000000),((-3412430775091653:ℚ)/48640000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((1398004653:ℚ)/2000000000),((7079333509:ℚ)/10000000000),((128:ℚ)/2269),((4706444503:ℚ)/37500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((12605593:ℚ)/31250000),((317288485387034150706762883549803766281862577136387499958471:ℚ)/11783663177490234375000000000000000000000000000000000000000000),((-13886096423304441:ℚ)/194560000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((7049513431:ℚ)/10000000000),((7138802423:ℚ)/10000000000),((8:ℚ)/143),((14178802423:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((478683567:ℚ)/1250000000),((12533482965464870688708694261443548182546810147169311849351:ℚ)/466557958101447265625000000000000000000000000000000000000000),((-70021385858896507:ℚ)/972800000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((7109001679:ℚ)/10000000000),((7198269787:ℚ)/10000000000),((128:ℚ)/2307),((14238269787:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((903554901:ℚ)/2500000000),((6952739667829722755292412979340906574756221870825700504022017:ℚ)/259389296359050000000000000000000000000000000000000000000000000),((-70612270550166163:ℚ)/972800000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((896061007:ℚ)/1250000000),((7257735639:ℚ)/10000000000),((64:ℚ)/1163),((14297735639:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3385955169:ℚ)/10000000000),((32133250917269987999599455043788080975878331188640548726789:ℚ)/1201347054450236328125000000000000000000000000000000000000000),((-8900392082146579:ℚ)/121600000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),(0:ℚ),((1:ℚ)/16),((7227972609:ℚ)/10000000000),((1463440003:ℚ)/2000000000),((128:ℚ)/2345),((2871440003:ℚ)/23260000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((314183499:ℚ)/1000000000),((2197940405349596671828476128268137047650842118494582393:ℚ)/82338694569531250000000000000000000000000000000000000000),((-3778630770881967:ℚ)/51200000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7287455381:ℚ)/10000000000),((7376662951:ℚ)/10000000000),((32:ℚ)/591),((14416662951:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2877821833:ℚ)/10000000000),((162761337447554720677411499040788977230679134259224442669743:ℚ)/6109013007478332519531250000000000000000000000000000000000000),((-72384814946030657:ℚ)/972800000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7346936417:ℚ)/10000000000),((11711851:ℚ)/15625000),((64:ℚ)/1201),((7570617:ℚ)/61562500),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2587828803:ℚ)/10000000000),((3500632592007053843995578283189034967315632768675789:ℚ)/131460352666056156158447265625000000000000000000000000),((-72975628001968349:ℚ)/972800000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((3732946721:ℚ)/5000000000),((7614500971:ℚ)/10000000000),((16:ℚ)/305),((14654500971:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((376273729:ℚ)/2000000000),((66822981339988293944223629634080944305599162309956678808683:ℚ)/2517959421609765625000000000000000000000000000000000000000000),((-37078601991508637:ℚ)/486400000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((3792422001:ℚ)/5000000000),((8090117431:ℚ)/10000000000),((4:ℚ)/81),((15130117431:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((39477777:ℚ)/625000000),((169401748863248129327590502070734845548680462413631490041:ℚ)/6357677343750000000000000000000000000000000000000000000000),((-37669357874266797:ℚ)/486400000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((4030293651:ℚ)/5000000000),((3122499:ℚ)/3125000),((1:ℚ)/25),((5322499:ℚ)/40500000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((14585075725213963588559488019267122846368601:ℚ)/540609741210937500000000000000000000000000000),((-9932797:ℚ)/128000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9962853157:ℚ)/10000000000),((13794201683:ℚ)/10000000000),((2:ℚ)/69),((20834201683:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3047038262995393607969088529057582349419:ℚ)/101568000000000000000000000000000000000000),((-9932797:ℚ)/128000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC17
#check @N11Formalization.C450Source12GroupedC17.bound
#print axioms N11Formalization.C450Source12GroupedC17.valid0
#print axioms N11Formalization.C450Source12GroupedC17.valid1
#print axioms N11Formalization.C450Source12GroupedC17.valid2
#print axioms N11Formalization.C450Source12GroupedC17.valid3
#print axioms N11Formalization.C450Source12GroupedC17.valid4
#print axioms N11Formalization.C450Source12GroupedC17.valid5
#print axioms N11Formalization.C450Source12GroupedC17.valid6
#print axioms N11Formalization.C450Source12GroupedC17.valid7
#print axioms N11Formalization.C450Source12GroupedC17.valid8
#print axioms N11Formalization.C450Source12GroupedC17.valid9
#print axioms N11Formalization.C450Source12GroupedC17.valid10
#print axioms N11Formalization.C450Source12GroupedC17.valid11
#print axioms N11Formalization.C450Source12GroupedC17.valid12
#print axioms N11Formalization.C450Source12GroupedC17.valid13
#print axioms N11Formalization.C450Source12GroupedC17.valid14
#print axioms N11Formalization.C450Source12GroupedC17.bound
#print axioms N11Formalization.C450Source12GroupedC17.endpoint_checks
