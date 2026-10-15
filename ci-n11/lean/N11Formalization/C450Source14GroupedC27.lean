import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((5830989817:ℚ)/10000000000),((6364474851:ℚ)/10000000000),((74145953:ℚ)/120000000),((78329223361:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1392553381:ℚ)/2000000000),((-8645342096266856373460351069:ℚ)/432000000000000000000000000000),((-90371679615669181165408547:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3153405129:ℚ)/5000000000),((825292127:ℚ)/1250000000),((3537405129:ℚ)/5530000000),((3372737799:ℚ)/4450000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5919692497:ℚ)/10000000000),((-26380388561359192224097113621191170693094421929701479:ℚ)/1056952356250000000000000000000000000000000000000000000),((-1414002409351633269921963:ℚ)/5776000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((409042381:ℚ)/625000000),((684017507:ℚ)/1000000000),((457042381:ℚ)/715000000),((8356192577:ℚ)/11060000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5332847767:ℚ)/10000000000),((-57659742206230828711854002461019670416369077991619:ℚ)/2284536718750000000000000000000000000000000000000000),((-905503474323341070727203:ℚ)/3696640000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((1695630361:ℚ)/2500000000),((1739771449:ℚ)/2500000000),((1887630361:ℚ)/2907500000),((1632114303:ℚ)/2200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4680781249:ℚ)/10000000000),((-3154266945363622819159316925436890697715739021645493:ℚ)/115212725610351562500000000000000000000000000000000000),((-5663255376424192449256347:ℚ)/23104000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((3450717343:ℚ)/5000000000),((3509269601:ℚ)/5000000000),((3834717343:ℚ)/5862500000),((42761965611:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((864222953:ℚ)/2000000000),((-57208839646599589564342387608237320602780462991671:ℚ)/2013803100585937500000000000000000000000000000000000),((-22660725378768249080777547:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6960889319:ℚ)/10000000000),((1415598269:ℚ)/2000000000),((7728889319:ℚ)/11820000000),((257247477:ℚ)/350000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4130358277:ℚ)/10000000000),((-24448915416868758116669325894749319378588050647405307:ℚ)/860104462500000000000000000000000000000000000000000000),((-3626250319750347955460067:ℚ)/14786560000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((702034267:ℚ)/1000000000),((1427488451:ℚ)/2000000000),((778834267:ℚ)/1191500000),((5788790987:ℚ)/7880000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((98272869:ℚ)/250000000),((-902040989837330318100169342016719165534536113941999:ℚ)/31716365360156250000000000000000000000000000000000000),((-3626783195029950780766947:ℚ)/14786560000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7079794769:ℚ)/10000000000),((7196891963:ℚ)/10000000000),((7847794769:ℚ)/12010000000),((87485811593:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((744276761:ℚ)/2000000000),((-19254812643306582680563861270586443261717538326568599:ℚ)/676688906640625000000000000000000000000000000000000000),((-90682867169803925730180243:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((3569622823:ℚ)/5000000000),((1451268099:ℚ)/2000000000),((3953622823:ℚ)/6052500000),((17627949089:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3499950009:ℚ)/10000000000),((-4383016673721589317427456972055934716884063697186873:ℚ)/153972053613281250000000000000000000000000000000000000),((-3627844795398617683643747:ℚ)/14786560000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((7198695329:ℚ)/10000000000),((182894697:ℚ)/250000000),((7966695329:ℚ)/12200000000),((2219841667:ℚ)/3026250000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((816046873:ℚ)/2500000000),((-323181108879148770419915927006700797767218303149258519:ℚ)/11349050000000000000000000000000000000000000000000000000),((-56693336268384629610923:ℚ)/231040000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7258143847:ℚ)/10000000000),((1486935863:ℚ)/2000000000),((8026143847:ℚ)/12390000000),((18020294493:ℚ)/24400000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((602145453:ℚ)/2000000000),((-27313291109834241345171195700286563452731838630993731:ℚ)/990632770312500000000000000000000000000000000000000000),((-3628729965525144710306043:ℚ)/14786560000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((922129687:ℚ)/1250000000),((7553566469:ℚ)/10000000000),((1018129687:ℚ)/1572500000),((91409231159:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1214120041:ℚ)/5000000000),((-655052862399881429061059019429120748553538687817:ℚ)/23732966327667236328125000000000000000000000000000),((-90744444207377799646005267:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((7495926797:ℚ)/10000000000),((3895664347:ℚ)/5000000000),((8263926797:ℚ)/12960000000),((47012307817:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1656816871:ℚ)/10000000000),((-13062354781901448173830693920526451346069775493578681:ℚ)/503884800000000000000000000000000000000000000000000000),((-3143208825388863:ℚ)/12800000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((3866846563:ℚ)/5000000000),((9692977537:ℚ)/10000000000),((4250846563:ℚ)/8000000000),((38314250969:ℚ)/43200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-5349471220586919397892883511235209354048640777891719:ℚ)/600000000000000000000000000000000000000000000000000000),((-31442649:ℚ)/128000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9635367767:ℚ)/10000000000),((3373728027:ℚ)/2500000000),((10403367767:ℚ)/22080000000),((39191008297:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((15564311630489471535089:ℚ)/5078400000000000000000000),((-31442649:ℚ)/128000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC27
#check @N11Formalization.C450Source14GroupedC27.bound
#print axioms N11Formalization.C450Source14GroupedC27.valid0
#print axioms N11Formalization.C450Source14GroupedC27.valid1
#print axioms N11Formalization.C450Source14GroupedC27.valid2
#print axioms N11Formalization.C450Source14GroupedC27.valid3
#print axioms N11Formalization.C450Source14GroupedC27.valid4
#print axioms N11Formalization.C450Source14GroupedC27.valid5
#print axioms N11Formalization.C450Source14GroupedC27.valid6
#print axioms N11Formalization.C450Source14GroupedC27.valid7
#print axioms N11Formalization.C450Source14GroupedC27.valid8
#print axioms N11Formalization.C450Source14GroupedC27.valid9
#print axioms N11Formalization.C450Source14GroupedC27.valid10
#print axioms N11Formalization.C450Source14GroupedC27.valid11
#print axioms N11Formalization.C450Source14GroupedC27.valid12
#print axioms N11Formalization.C450Source14GroupedC27.valid13
#print axioms N11Formalization.C450Source14GroupedC27.valid14
#print axioms N11Formalization.C450Source14GroupedC27.bound
#print axioms N11Formalization.C450Source14GroupedC27.endpoint_checks
