import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6078183023:ℚ)/10000000000),((3302183959:ℚ)/5000000000),((5439394341:ℚ)/35600000000),((6022183959:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6438994631:ℚ)/10000000000),((889017191712392854208373378438729933889:ℚ)/15102368704000000000000000000000000000000),((-4101917492640142833605943:ℚ)/23104000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((1311163393:ℚ)/2000000000),((342146249:ℚ)/500000000),((3359163393:ℚ)/22120000000),((614146249:ℚ)/2670000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5303946487:ℚ)/10000000000),((3044816878600871612091271027496279979538972292616404410879:ℚ)/54570172058128125000000000000000000000000000000000000000000),((-43641244763887886802903:ℚ)/231040000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6794497163:ℚ)/10000000000),((6962176561:ℚ)/10000000000),((1892721907:ℚ)/12500000000),((12402176561:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1161433483:ℚ)/2500000000),((52152723474036061721567696587302152121363911279705149:ℚ)/955653125000000000000000000000000000000000000000000000),((-17980304764588964887641063:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((138276143:ℚ)/200000000),((7081411379:ℚ)/10000000000),((343076143:ℚ)/2288000000),((1391267931:ℚ)/6250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((856415303:ℚ)/2000000000),((846324862522964760175637570219337453280762259951182388143:ℚ)/15601348876953125000000000000000000000000000000000000000000),((-18236098644044136052393823:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((7033098409:ℚ)/10000000000),((7200630263:ℚ)/10000000000),((17273098409:ℚ)/116300000000),((12640630263:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3886863787:ℚ)/10000000000),((10669592192316882919852682169816692540624773547108498828356499:ℚ)/197759586889150000000000000000000000000000000000000000000000000),((-18491650339606031085247607:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((3576185933:ℚ)/5000000000),((1463966797:ℚ)/2000000000),((8696185933:ℚ)/59100000000),((2551966797:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1724613961:ℚ)/5000000000),((7681655933160982330001327046893925132915502829595719846107:ℚ)/143081301382788281250000000000000000000000000000000000000000),((-749878477179254913733727:ℚ)/3696640000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3635814193:ℚ)/5000000000),((929877909:ℚ)/1250000000),((8755814193:ℚ)/60050000000),((1609877909:ℚ)/7387500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2950307259:ℚ)/10000000000),((291406750662482916367966405748211679728430923776905375959731:ℚ)/5451923745766680908203125000000000000000000000000000000000000),((-296906802414640930191743:ℚ)/1444000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7390868781:ℚ)/10000000000),((3779099401:ℚ)/5000000000),((17630868781:ℚ)/122000000000),((6499099401:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((18369977:ℚ)/78125000),((16756869673971714934374183264673876348738241359576992901813:ℚ)/314744927701220703125000000000000000000000000000000000000000),((-4814218109264924578189303:ℚ)/23104000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7510093809:ℚ)/10000000000),((8034775541:ℚ)/10000000000),((17750093809:ℚ)/129600000000),((13474775541:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((769842833:ℚ)/5000000000),((63001721856448714015169495771204156853308924826562647065353:ℚ)/1163454953906250000000000000000000000000000000000000000000000),((-25684029797638933:ℚ)/121600000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((3993426937:ℚ)/5000000000),((621223697:ℚ)/625000000),((9113426937:ℚ)/80000000000),((106802633:ℚ)/450000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6078442499561168488187823343849786220760613000639:ℚ)/106787109375000000000000000000000000000000000000000),((-6828799:ℚ)/32000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((989221529:ℚ)/1000000000),((3436302367:ℚ)/2500000000),((671073843:ℚ)/7360000000),((4796302367:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((35152900311577186323923710664938265417:ℚ)/529000000000000000000000000000000000000),((-6828799:ℚ)/32000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC18
#check @N11Formalization.C450Source18GroupedC18.bound
#print axioms N11Formalization.C450Source18GroupedC18.valid0
#print axioms N11Formalization.C450Source18GroupedC18.valid1
#print axioms N11Formalization.C450Source18GroupedC18.valid2
#print axioms N11Formalization.C450Source18GroupedC18.valid3
#print axioms N11Formalization.C450Source18GroupedC18.valid4
#print axioms N11Formalization.C450Source18GroupedC18.valid5
#print axioms N11Formalization.C450Source18GroupedC18.valid6
#print axioms N11Formalization.C450Source18GroupedC18.valid7
#print axioms N11Formalization.C450Source18GroupedC18.valid8
#print axioms N11Formalization.C450Source18GroupedC18.valid9
#print axioms N11Formalization.C450Source18GroupedC18.valid10
#print axioms N11Formalization.C450Source18GroupedC18.bound
#print axioms N11Formalization.C450Source18GroupedC18.endpoint_checks
