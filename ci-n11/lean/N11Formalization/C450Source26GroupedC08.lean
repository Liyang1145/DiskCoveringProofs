import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((3312002603:ℚ)/5000000000),((6826923983:ℚ)/10000000000),((-46082315847:ℚ)/99200000000),((-2312002603:ℚ)/6318750000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5123811073:ℚ)/10000000000),((33021805278623944113167733139865354207524082840849254751:ℚ)/146641361668395996093750000000000000000000000000000000000),((15368296142404882571255307:ℚ)/73932800000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((134876337:ℚ)/200000000),((6946684563:ℚ)/10000000000),((-15720053689:ℚ)/33700000000),((-94876337:ℚ)/257500000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4792428117:ℚ)/10000000000),((24315967762894347059527844376487406394256509177644707:ℚ)/107885448925781250000000000000000000000000000000000000),((24063843288237439392387:ℚ)/118292480000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((343179441:ℚ)/500000000),((3503275413:ℚ)/5000000000),((-23849478717:ℚ)/51500000000),((-243179441:ℚ)/649687500),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4438530343:ℚ)/10000000000),((2672916417660433985511671652647939103119553921435971:ℚ)/12036475975084304809570312500000000000000000000000000),((147088240961919508613763:ℚ)/739328000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((3461730309:ℚ)/5000000000),((3533204041:ℚ)/5000000000),((-8039612123:ℚ)/17325000000),((-2461730309:ℚ)/6556250000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4251383973:ℚ)/10000000000),((67807312018695533263378238241799442531034700207077946457:ℚ)/305154498961257934570312500000000000000000000000000000000),((14542277606449406871662763:ℚ)/73932800000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6983323307:ℚ)/10000000000),((7126256579:ℚ)/10000000000),((-48776309211:ℚ)/104900000000),((-4983323307:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4056189841:ℚ)/10000000000),((3376590018030418274799811171656570837611819815932804087403:ℚ)/15186515286311340332031250000000000000000000000000000000000),((57500235628659441062838027:ℚ)/295731200000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((1408635427:ℚ)/2000000000),((898262069:ℚ)/1250000000),((-6164358621:ℚ)/13231250000),((-336211809:ℚ)/890000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((962929929:ℚ)/2500000000),((518784911792831124262963419999686920403107656093277557:ℚ)/2331905270312500000000000000000000000000000000000000000),((2273146819144189424583867:ℚ)/11829248000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((887877793:ℚ)/1250000000),((3608006707:ℚ)/5000000000),((-8264020121:ℚ)/17800000000),((-91125399:ℚ)/239453125),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((45455051:ℚ)/125000000),((105450948395220453016409065970302029352078282202651:ℚ)/477322128904052078723907470703125000000000000000000),((877412710659552769153827:ℚ)/4620800000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((1783235447:ℚ)/2500000000),((7245928231:ℚ)/10000000000),((-49853354079:ℚ)/107275000000),((-1283235447:ℚ)/3367187500),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1762030153:ℚ)/5000000000),((883860541139634145680552553045328492695899425207480607:ℚ)/3999451808410231024026870727539062500000000000000000000),((3488517194238442583021907:ℚ)/18483200000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1790714791:ℚ)/2500000000),((3652875919:ℚ)/5000000000),((-25195883271:ℚ)/53875000000),((-1290714791:ℚ)/3396875000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1704091329:ℚ)/5000000000),((23516001887056458959034602342780973569524880908705696849:ℚ)/105583483084297180175781250000000000000000000000000000000),((3467341452301090971981363:ℚ)/18483200000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7222687819:ℚ)/10000000000),((230173987:ℚ)/312500000),((-1591565883:ℚ)/3396875000),((-5222687819:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1582129257:ℚ)/5000000000),((324852890492667557128678515267537321103274787341822015959:ℚ)/1457754069386672973632812500000000000000000000000000000000),((54797818365033213943408203:ℚ)/295731200000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((291300341:ℚ)/400000000),((297015027:ℚ)/400000000),((-686245081:ℚ)/1462000000),((-30185763:ℚ)/79000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((362583351:ℚ)/1250000000),((7847461425448642217998461998609960113413194641017:ℚ)/35196436425781250000000000000000000000000000000000),((86584764062420021321163:ℚ)/473169920000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((7342321489:ℚ)/10000000000),((7544969681:ℚ)/10000000000),((-52544727129:ℚ)/110600000000),((-5342321489:ℚ)/14062500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1305726061:ℚ)/5000000000),((25482207023162474091246468545651336970033615325896445099:ℚ)/112635176628828048706054687500000000000000000000000000000),((53430439493805868367868483:ℚ)/295731200000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7461924987:ℚ)/10000000000),((3832267681:ℚ)/5000000000),((-8936803043:ℚ)/18750000000),((-5461924987:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1909085869:ℚ)/10000000000),((1128360879550860031538798669217108307374608326300435531:ℚ)/4984443750000000000000000000000000000000000000000000000),((52052266862767474275062187:ℚ)/295731200000000000000000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((7581499839:ℚ)/10000000000),((538762023:ℚ)/625000000),((-299142939:ℚ)/550000000),((-5581499839:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((69788537:ℚ)/1000000000),((25887420822927150444589241063095618798751019090844991407:ℚ)/97430850000000000000000000000000000000000000000000000000),((50663291103593242324550883:ℚ)/295731200000000000000000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((4268610181:ℚ)/5000000000),((5264130851:ℚ)/5000000000),((-13232392553:ℚ)/21600000000),((-3268610181:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((49777427291241076653688985468496574355311396956386195423:ℚ)/168750000000000000000000000000000000000000000000000000000),((87339681:ℚ)/512000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((10445380071:ℚ)/10000000000),((14337709847:ℚ)/10000000000),((-113679388623:ℚ)/160000000000),((-8445380071:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((10706698798956181079235819643175565315912676284608913591880783:ℚ)/30470400000000000000000000000000000000000000000000000000000000),((87339681:ℚ)/512000000)⟩
theorem valid15 : Valid source26 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((45:ℚ)/64) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC08
#check @N11Formalization.C450Source26GroupedC08.bound
#print axioms N11Formalization.C450Source26GroupedC08.valid0
#print axioms N11Formalization.C450Source26GroupedC08.valid1
#print axioms N11Formalization.C450Source26GroupedC08.valid2
#print axioms N11Formalization.C450Source26GroupedC08.valid3
#print axioms N11Formalization.C450Source26GroupedC08.valid4
#print axioms N11Formalization.C450Source26GroupedC08.valid5
#print axioms N11Formalization.C450Source26GroupedC08.valid6
#print axioms N11Formalization.C450Source26GroupedC08.valid7
#print axioms N11Formalization.C450Source26GroupedC08.valid8
#print axioms N11Formalization.C450Source26GroupedC08.valid9
#print axioms N11Formalization.C450Source26GroupedC08.valid10
#print axioms N11Formalization.C450Source26GroupedC08.valid11
#print axioms N11Formalization.C450Source26GroupedC08.valid12
#print axioms N11Formalization.C450Source26GroupedC08.valid13
#print axioms N11Formalization.C450Source26GroupedC08.valid14
#print axioms N11Formalization.C450Source26GroupedC08.valid15
#print axioms N11Formalization.C450Source26GroupedC08.bound
#print axioms N11Formalization.C450Source26GroupedC08.endpoint_checks
