import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((763250847:ℚ)/1250000000),((6609795803:ℚ)/10000000000),((843250847:ℚ)/2670000000),((21749387409:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6377759861:ℚ)/10000000000),((5798341023373981733175607757295107820437:ℚ)/1087370546688000000000000000000000000000000),((-1198852109019137021747659:ℚ)/17328000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3290645551:ℚ)/5000000000),((5477911:ℚ)/8000000),((3610645551:ℚ)/11060000000),((5989911:ℚ)/14240000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5237308573:ℚ)/10000000000),((12748743681000753229246872686320434264407063271129:ℚ)/2759499070988800000000000000000000000000000000000000),((-6508229184137419583578617:ℚ)/92416000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((34094593:ℚ)/50000000),((6966182867:ℚ)/10000000000),((12431531:ℚ)/37500000),((22818548601:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2286746387:ℚ)/5000000000),((2929900953288052506380650311710764118494201154336750353:ℚ)/679469371875000000000000000000000000000000000000000000000),((-656599776001361468633:ℚ)/9241600000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((1734432279:ℚ)/2500000000),((7025579371:ℚ)/10000000000),((1894432279:ℚ)/5672500000),((7665579371:ℚ)/18750000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2102816621:ℚ)/5000000000),((442102702221245318996333921856100295418949572942115536002429:ℚ)/106052968597412109375000000000000000000000000000000000000000000),((-4946272775870852801916091:ℚ)/69312000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((6997133613:ℚ)/10000000000),((3542487759:ℚ)/5000000000),((7637133613:ℚ)/22880000000),((11587463277:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2004944149:ℚ)/5000000000),((10979791053560964396785738901752467921518102814484771659:ℚ)/2650897489212768554687500000000000000000000000000000000000),((-79315005131072558481174019:ℚ)/1108992000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((7056537621:ℚ)/10000000000),((7144371317:ℚ)/10000000000),((7696537621:ℚ)/23070000000),((23353113951:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3804657137:ℚ)/10000000000),((1067730351185904153733004612084476453931931991384458248936003:ℚ)/259389296359050000000000000000000000000000000000000000000000000),((-79489942605562544098171891:ℚ)/1108992000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((142318823:ℚ)/200000000),((288150671:ℚ)/400000000),((155118823:ℚ)/465200000),((313750671:ℚ)/769000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3588308483:ℚ)/10000000000),((314610100023261044468226772833724431099016752811696089:ℚ)/76886211484815125000000000000000000000000000000000000000),((-10622023581275157285193:ℚ)/147865600000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/16),((3:ℚ)/8),((7175344213:ℚ)/10000000000),((3631580951:ℚ)/5000000000),((7815344213:ℚ)/23450000000),((11854742853:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3358690431:ℚ)/10000000000),((17184570414714584792725699692573430814450337244971940815163:ℚ)/4223717722996423339843750000000000000000000000000000000000000),((-26613569308103056137809873:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((361737341:ℚ)/500000000),((1464511341:ℚ)/2000000000),((393737341:ℚ)/1182000000),((4777534023:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((622572693:ℚ)/2000000000),((1779797243000720917417974579836633304371843152610056616833:ℚ)/439848936538439941406250000000000000000000000000000000000000),((-66680446518671630374177:ℚ)/924160000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((911768623:ℚ)/1250000000),((922743899:ℚ)/1250000000),((991768623:ℚ)/2978750000),((1002743899:ℚ)/2462500000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2846626547:ℚ)/10000000000),((3199930167642861454989292120196419669677352135596811266623:ℚ)/794965128588812255859375000000000000000000000000000000000000),((-417670107216480334588793:ℚ)/5776000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((3676775357:ℚ)/5000000000),((7441345371:ℚ)/10000000000),((3996775357:ℚ)/12010000000),((24244036113:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2553598509:ℚ)/10000000000),((238576117450050705714248941576595582227146715154634142839847:ℚ)/59567339989394186401367187500000000000000000000000000000000000),((-6697423519488773624899233:ℚ)/92416000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((7412952021:ℚ)/10000000000),((236254151:ℚ)/312500000),((8052952021:ℚ)/24400000000),((768762453:ℚ)/1876562500),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2223204851:ℚ)/10000000000),((39973556052004980063261158632984686084250591162927210361:ℚ)/9835778990663146972656250000000000000000000000000000000000),((-80545800793526207150616691:ℚ)/1108992000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1506350681:ℚ)/2000000000),((7797704357:ℚ)/10000000000),((1634350681:ℚ)/5032000000),((25313113071:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((335285083:ℚ)/2500000000),((293002251661545138747168669373636116738771878780778587847481:ℚ)/70158585797656250000000000000000000000000000000000000000000000),((-1078668383172836623355337:ℚ)/14786560000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((7769351513:ℚ)/10000000000),((8035271687:ℚ)/10000000000),((2803117171:ℚ)/8640000000),((26025815061:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2329674306375201307670784248480658139185759537702839103971:ℚ)/566930061815625000000000000000000000000000000000000000000000),((-9361059:ℚ)/128000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((1601388773:ℚ)/2000000000),((620980947:ℚ)/625000000),((1729388773:ℚ)/6400000000),((660980947:ℚ)/1350000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((32031497479422131579656577399129621338440218186069:ℚ)/5766503906250000000000000000000000000000000000000000),((-9361059:ℚ)/128000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((9907524691:ℚ)/10000000000),((3434048049:ℚ)/2500000000),((10547524691:ℚ)/44160000000),((10782144147:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((720202825828888732675847:ℚ)/97505280000000000000000000),((-9361059:ℚ)/128000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC22
#check @N11Formalization.C450SeventhGroupedC22.bound
#print axioms N11Formalization.C450SeventhGroupedC22.valid0
#print axioms N11Formalization.C450SeventhGroupedC22.valid1
#print axioms N11Formalization.C450SeventhGroupedC22.valid2
#print axioms N11Formalization.C450SeventhGroupedC22.valid3
#print axioms N11Formalization.C450SeventhGroupedC22.valid4
#print axioms N11Formalization.C450SeventhGroupedC22.valid5
#print axioms N11Formalization.C450SeventhGroupedC22.valid6
#print axioms N11Formalization.C450SeventhGroupedC22.valid7
#print axioms N11Formalization.C450SeventhGroupedC22.valid8
#print axioms N11Formalization.C450SeventhGroupedC22.valid9
#print axioms N11Formalization.C450SeventhGroupedC22.valid10
#print axioms N11Formalization.C450SeventhGroupedC22.valid11
#print axioms N11Formalization.C450SeventhGroupedC22.valid12
#print axioms N11Formalization.C450SeventhGroupedC22.valid13
#print axioms N11Formalization.C450SeventhGroupedC22.valid14
#print axioms N11Formalization.C450SeventhGroupedC22.valid15
#print axioms N11Formalization.C450SeventhGroupedC22.bound
#print axioms N11Formalization.C450SeventhGroupedC22.endpoint_checks
