import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((1365934939:ℚ)/2500000000),((1204367243:ℚ)/2000000000),((18493651:ℚ)/25000000),((18472774159:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7685588981:ℚ)/10000000000),((-9069945392177088820149650353:ℚ)/48828125000000000000000000000),((-403216304310597682885961:ℚ)/1155200000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((2970128659:ℚ)/5000000000),((6260134707:ℚ)/10000000000),((10590385977:ℚ)/13825000000),((95461751191:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1683872701:ℚ)/2500000000),((-864874245798300683177123287122430432240052530010031561:ℚ)/4128720141601562500000000000000000000000000000000000000),((-9928182688426185486283161:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((6178437547:ℚ)/10000000000),((6379263627:ℚ)/10000000000),((7298437547:ℚ)/9375000000),((97010427151:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((388495117:ℚ)/625000000),((-10521943179698312821859419289723278407645254167408977:ℚ)/47683715820312500000000000000000000000000000000000000),((-9851337595635354252471081:ℚ)/28880000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((3148755179:ℚ)/5000000000),((6498379903:ℚ)/10000000000),((11126265537:ℚ)/14300000000),((98558938739:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2970793303:ℚ)/5000000000),((-91536531791972994969825453255044632220142312792646059:ℚ)/415370312500000000000000000000000000000000000000000000),((-9774003716384222025034001:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1283314481:ℚ)/2000000000),((6617484157:ℚ)/10000000000),((4521943443:ℚ)/5815000000),((100107294041:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((565565211:ℚ)/1000000000),((-16904982191699859721196917322478756323790815051761179:ℚ)/76808483740234375000000000000000000000000000000000000),((-9696180801200262623260361:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((816953027:ℚ)/1250000000),((6677031959:ℚ)/10000000000),((42848643:ℚ)/54687500),((100881415467:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5356235423:ℚ)/10000000000),((-2056258040079938967221680113055283609031263793:ℚ)/9126961231231689453125000000000000000000000000),((-9657085881646668931303009:ℚ)/28880000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((164878661:ℚ)/250000000),((1684144243:ℚ)/2500000000),((192878661:ℚ)/246250000),((25413875159:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5200739637:ℚ)/10000000000),((-1313003915156738325806463610935805230007892655333:ℚ)/5832956695556640625000000000000000000000000000000),((-601116788496486093512711:ℚ)/1805000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6654666289:ℚ)/10000000000),((6796119263:ℚ)/10000000000),((23323998867:ℚ)/29787500000),((34143183473:ℚ)/39400000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1008181621:ℚ)/2000000000),((-9288182494772800972629043634407964368358459674376794851:ℚ)/41297350729370117187500000000000000000000000000000000000),((-9578528977203198225122641:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((335709191:ℚ)/500000000),((428478681:ℚ)/625000000),((1175127573:ℚ)/1501250000),((6450222853:ℚ)/7446875000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((195052447:ℚ)/400000000),((-74251317266598953437805395235909009489373597100389:ℚ)/330414505195617675781250000000000000000000000000000),((-74523960468502951385883:ℚ)/225625000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((423356193:ℚ)/625000000),((3487365219:ℚ)/5000000000),((1480068579:ℚ)/1906250000),((52375747847:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4706445489:ℚ)/10000000000),((-2373426666849374114187772301878882060109477724440643:ℚ)/10823297500610351562500000000000000000000000000000000),((-2364943892381256865272429:ℚ)/7220000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6892723047:ℚ)/10000000000),((88672401:ℚ)/125000000),((1144674721:ℚ)/1475000000),((1328741213:ℚ)/1525000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((4348405067:ℚ)/10000000000),((-274563947474032524542256053767427180966688617840897:ℚ)/1253533935546875000000000000000000000000000000000000),((-2931248222034739237503:ℚ)/9025000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((438233661:ℚ)/625000000),((7212844273:ℚ)/10000000000),((1524700983:ℚ)/1965625000),((107846975549:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3960365881:ℚ)/10000000000),((-149135489921051997310177759329734055169830448263:ℚ)/681668380275368690490722656250000000000000000000),((-9299722981740738840983681:ℚ)/28880000000000000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((3565373029:ℚ)/5000000000),((372546099:ℚ)/500000000),((458374781:ℚ)/600000000),((5547099287:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3532421251:ℚ)/10000000000),((-7837475006380676343835699205977171700471294711557:ℚ)/37500000000000000000000000000000000000000000000000),((-22844273614116322655439:ℚ)/72200000000000000000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((14392067:ℚ)/19531250),((584659567:ℚ)/625000000),((49738701:ℚ)/78125000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1236623581:ℚ)/5000000000),((-5287187923009469940633543617882546294425033773:ℚ)/46566128730773925781250000000000000000000000000),((-4004543:ℚ)/12800000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((4635916289:ℚ)/5000000000),((3289702671:ℚ)/2500000000),((5195916289:ℚ)/9200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2759583934180552631337551696919971:ℚ)/48668000000000000000000000000000000),((-4004543:ℚ)/12800000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC29
#check @N11Formalization.C450Source23GroupedC29.bound
#print axioms N11Formalization.C450Source23GroupedC29.valid0
#print axioms N11Formalization.C450Source23GroupedC29.valid1
#print axioms N11Formalization.C450Source23GroupedC29.valid2
#print axioms N11Formalization.C450Source23GroupedC29.valid3
#print axioms N11Formalization.C450Source23GroupedC29.valid4
#print axioms N11Formalization.C450Source23GroupedC29.valid5
#print axioms N11Formalization.C450Source23GroupedC29.valid6
#print axioms N11Formalization.C450Source23GroupedC29.valid7
#print axioms N11Formalization.C450Source23GroupedC29.valid8
#print axioms N11Formalization.C450Source23GroupedC29.valid9
#print axioms N11Formalization.C450Source23GroupedC29.valid10
#print axioms N11Formalization.C450Source23GroupedC29.valid11
#print axioms N11Formalization.C450Source23GroupedC29.valid12
#print axioms N11Formalization.C450Source23GroupedC29.valid13
#print axioms N11Formalization.C450Source23GroupedC29.valid14
#print axioms N11Formalization.C450Source23GroupedC29.bound
#print axioms N11Formalization.C450Source23GroupedC29.endpoint_checks
