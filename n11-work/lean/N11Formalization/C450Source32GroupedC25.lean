import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/2),((9:ℚ)/16),((270857343:ℚ)/500000000),((1438265687:ℚ)/2500000000),((390857343:ℚ)/643750000),((17904391183:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3886694743:ℚ)/5000000000),((-194602563209879970000443157340364012696651317070578617007577:ℚ)/606821220480000000000000000000000000000000000000000000000000),((-386376745753509016668213:ℚ)/902500000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((5657837321:ℚ)/10000000000),((5993604859:ℚ)/10000000000),((8057837321:ℚ)/13350000000),((73782443731:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7310822013:ℚ)/10000000000),((-2586948828147196869771111392336723339408051135560446711210029:ℚ)/8114522406562500000000000000000000000000000000000000000000000),((-3059872037673179881936181:ℚ)/7220000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((5898296481:ℚ)/10000000000),((6113794687:ℚ)/10000000000),((8298296481:ℚ)/13587500000),((74864152183:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6823520097:ℚ)/10000000000),((-194554118341168073565732669110345264910606390079878587569810513:ℚ)/599738051779920000000000000000000000000000000000000000000000000),((-3056955395390820030456669:ℚ)/7220000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6018447087:ℚ)/10000000000),((6233934173:ℚ)/10000000000),((8418447087:ℚ)/13825000000),((75945407557:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((131376123:ℚ)/200000000),((-7441684306667089967843993748771505879656599633087709399167867:ℚ)/23013898248452753906250000000000000000000000000000000000000000),((-3039905690349174063868129:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6138548747:ℚ)/10000000000),((6354025927:ℚ)/10000000000),((8538548747:ℚ)/14062500000),((77026233343:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6305492777:ℚ)/10000000000),((-8213780912795044790112338949668872982374525219139675431:ℚ)/25480101445312500000000000000000000000000000000000000000),((-3022267865328169888428529:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((3129301997:ℚ)/5000000000),((323703619:ℚ)/500000000),((4329301997:ℚ)/7150000000),((3905332571:ℚ)/5625000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1508105813:ℚ)/2500000000),((-1462211673815051497570323089363288716994370984331170313207:ℚ)/4549353332519531250000000000000000000000000000000000000000),((-30040422657436071635469:ℚ)/72200000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((797326899:ℚ)/1250000000),((6594075799:ℚ)/10000000000),((1097326899:ℚ)/1817187500),((79186682191:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((574817621:ℚ)/1000000000),((-73754867276970330038788973902914018893260902291030325720974993:ℚ)/230120246561920000000000000000000000000000000000000000000000000),((-157117327061667760458129:ℚ)/380000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((1299716909:ℚ)/2000000000),((3357019151:ℚ)/5000000000),((1779716909:ℚ)/2955000000),((40133172359:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5450971669:ℚ)/10000000000),((-762251550819947775860224315380297565495512738934543286347483:ℚ)/2384688356379804687500000000000000000000000000000000000000000),((-1482914505655175123321827:ℚ)/3610000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((661851411:ℚ)/1000000000),((6833961871:ℚ)/10000000000),((901851411:ℚ)/1501250000),((81345656839:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((256926467:ℚ)/500000000),((-711969915857451443066344489402750462430880271534963045115671601:ℚ)/2233107966266032500000000000000000000000000000000000000000000000),((-2945841937503320717626191:ℚ)/7220000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((3369202907:ℚ)/5000000000),((6953848359:ℚ)/10000000000),((4569202907:ℚ)/7625000000),((82424635231:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4807845871:ℚ)/10000000000),((-7687946484590766600848559989240438209886598731509019841544889:ℚ)/24172410447453750000000000000000000000000000000000000000000000),((-8775804768131754161601293:ℚ)/21660000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3429130729:ℚ)/5000000000),((359675847:ℚ)/500000000),((4629130729:ℚ)/7862500000),((4229082623:ℚ)/6100000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2227412977:ℚ)/5000000000),((-26221665097351785582626653696781479816070432014498865415097:ℚ)/84190302957187500000000000000000000000000000000000000000000),((-86065995856830471756683:ℚ)/216600000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((354893561:ℚ)/500000000),((3716528353:ℚ)/5000000000),((474893561:ℚ)/810000000),((43368755177:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1827706277:ℚ)/5000000000),((-5707041931247601942030033892453514079331833276784222195699:ℚ)/18386920923750000000000000000000000000000000000000000000000),((-705905963681049223968309:ℚ)/1805000000000000000000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((3668677853:ℚ)/5000000000),((934585341:ℚ)/1000000000),((4868677853:ℚ)/10000000000),((10395268069:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1318320193:ℚ)/5000000000),((-1963911080703028029166748824301212882339679520575293211:ℚ)/8162933760000000000000000000000000000000000000000000000),((-94277341999510131:ℚ)/243200000000000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((115622581:ℚ)/125000000),((3290203483:ℚ)/2500000000),((145622581:ℚ)/345000000),((34571831347:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2035416240041861350238298846962848550064362233648757919511:ℚ)/10580000000000000000000000000000000000000000000000000000000),((-25072047:ℚ)/64000000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC25
#check @N11Formalization.C450Source32GroupedC25.bound
#print axioms N11Formalization.C450Source32GroupedC25.valid0
#print axioms N11Formalization.C450Source32GroupedC25.valid1
#print axioms N11Formalization.C450Source32GroupedC25.valid2
#print axioms N11Formalization.C450Source32GroupedC25.valid3
#print axioms N11Formalization.C450Source32GroupedC25.valid4
#print axioms N11Formalization.C450Source32GroupedC25.valid5
#print axioms N11Formalization.C450Source32GroupedC25.valid6
#print axioms N11Formalization.C450Source32GroupedC25.valid7
#print axioms N11Formalization.C450Source32GroupedC25.valid8
#print axioms N11Formalization.C450Source32GroupedC25.valid9
#print axioms N11Formalization.C450Source32GroupedC25.valid10
#print axioms N11Formalization.C450Source32GroupedC25.valid11
#print axioms N11Formalization.C450Source32GroupedC25.valid12
#print axioms N11Formalization.C450Source32GroupedC25.valid13
#print axioms N11Formalization.C450Source32GroupedC25.bound
#print axioms N11Formalization.C450Source32GroupedC25.endpoint_checks
