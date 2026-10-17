import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/2),((9:ℚ)/16),((5389009737:ℚ)/10000000000),((5727299133:ℚ)/10000000000),((7869009737:ℚ)/12875000000),((72025692197:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3913016893:ℚ)/5000000000),((-63639059039032847336171466719171703498916763699250082418321:ℚ)/188526981120000000000000000000000000000000000000000000000000),((-6270417012181171604989579:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((45039311:ℚ)/80000000),((5968051687:ℚ)/10000000000),((21626437:ℚ)/35600000),((74192465183:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3682841637:ℚ)/5000000000),((-5102513995144577090507851391969220000360624395504798160999:ℚ)/15195734843750000000000000000000000000000000000000000000000),((-6205194008082043792909159:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((2935285457:ℚ)/5000000000),((6088341009:ℚ)/10000000000),((4175285457:ℚ)/6793750000),((75275069081:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((86014567:ℚ)/125000000),((-94428757370482085079506413902543504278234944845928914926677:ℚ)/275868469080000000000000000000000000000000000000000000000000),((-6197590323577294162659141:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((5990815079:ℚ)/10000000000),((3104288223:ℚ)/5000000000),((8470815079:ℚ)/13825000000),((38178594007:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1325623623:ℚ)/2000000000),((-126806096017199472260898614178798031296500575138328416747:ℚ)/371575469007568359375000000000000000000000000000000000000),((-3080973456939288240708913:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6111006969:ℚ)/10000000000),((1582190199:ℚ)/2500000000),((8591006969:ℚ)/14062500000),((2765673113:ℚ)/3950000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((397918859:ℚ)/625000000),((-460800644658793089223608381530493856312136570102609:ℚ)/1354172058105468750000000000000000000000000000000000),((-3062548950833212162547513:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((1246229859:ℚ)/2000000000),((6448896663:ℚ)/10000000000),((1742229859:ℚ)/2860000000),((78520069967:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((6095808469:ℚ)/10000000000),((-43183095765225267559457094197709301829811255127742235236737:ℚ)/127254638671875000000000000000000000000000000000000000000000),((-6087044028765003118069759:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((793905573:ℚ)/1250000000),((6568986479:ℚ)/10000000000),((1103905573:ℚ)/1817187500),((79600878311:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2907041153:ℚ)/5000000000),((-33484235571442553675320142454284090932489125130189335468631:ℚ)/98933897920000000000000000000000000000000000000000000000000),((-6047785985097192377359601:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6471295191:ℚ)/10000000000),((3344516257:ℚ)/5000000000),((8951295191:ℚ)/14775000000),((40340646313:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5519832833:ℚ)/10000000000),((-6130000934886814385459159663432662502833362437653060672591:ℚ)/18157525556191406250000000000000000000000000000000000000000),((-3003662207267235260849953:ℚ)/7220000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3295651659:ℚ)/5000000000),((6809036889:ℚ)/10000000000),((4535651659:ℚ)/7506250000),((81761332001:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5210906281:ℚ)/10000000000),((-313113579046815847814635257863161845976315871505798546688019:ℚ)/929686913516250000000000000000000000000000000000000000000000),((-5965659919958815091406781:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((419454439:ℚ)/625000000),((866125199:ℚ)/1250000000),((574454439:ℚ)/953125000),((10355126791:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1221121227:ℚ)/2500000000),((-130037467111200054409876923011381547564275160468594242809:ℚ)/386981468485107421875000000000000000000000000000000000000),((-185087283242453325946097:ℚ)/451250000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6831200233:ℚ)/10000000000),((7168819313:ℚ)/10000000000),((9311200233:ℚ)/15725000000),((84999373817:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((4536758927:ℚ)/10000000000),((-176054797163931540811587512202924045907352848262422416890047:ℚ)/535391433750000000000000000000000000000000000000000000000000),((-5806724720874015199802659:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((7070950277:ℚ)/10000000000),((185212481:ℚ)/250000000),((9550950277:ℚ)/16200000000),((2178912329:ℚ)/3145000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1876629637:ℚ)/5000000000),((-13953381153286831926640594148600167200612986943244381:ℚ)/42562316953125000000000000000000000000000000000000000),((-114251954234358071608197:ℚ)/288800000000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((7310566603:ℚ)/10000000000),((9322172803:ℚ)/10000000000),((9790566603:ℚ)/20000000000),((104379555227:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((692166441:ℚ)/2500000000),((-1018825123495240190314206100448674803600384082776209730377:ℚ)/4081466880000000000000000000000000000000000000000000000000),((-76053808234984333:ℚ)/194560000000000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((9223842313:ℚ)/10000000000),((3284538487:ℚ)/2500000000),((3901280771:ℚ)/9200000000),((34680846383:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-7189034126820930947144141086218638739:ℚ)/36800000000000000000000000000000000000),((-10121479:ℚ)/25600000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC25
#check @N11Formalization.C450Source33GroupedC25.bound
#print axioms N11Formalization.C450Source33GroupedC25.valid0
#print axioms N11Formalization.C450Source33GroupedC25.valid1
#print axioms N11Formalization.C450Source33GroupedC25.valid2
#print axioms N11Formalization.C450Source33GroupedC25.valid3
#print axioms N11Formalization.C450Source33GroupedC25.valid4
#print axioms N11Formalization.C450Source33GroupedC25.valid5
#print axioms N11Formalization.C450Source33GroupedC25.valid6
#print axioms N11Formalization.C450Source33GroupedC25.valid7
#print axioms N11Formalization.C450Source33GroupedC25.valid8
#print axioms N11Formalization.C450Source33GroupedC25.valid9
#print axioms N11Formalization.C450Source33GroupedC25.valid10
#print axioms N11Formalization.C450Source33GroupedC25.valid11
#print axioms N11Formalization.C450Source33GroupedC25.valid12
#print axioms N11Formalization.C450Source33GroupedC25.valid13
#print axioms N11Formalization.C450Source33GroupedC25.bound
#print axioms N11Formalization.C450Source33GroupedC25.endpoint_checks
