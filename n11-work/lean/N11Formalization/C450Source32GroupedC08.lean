import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6712282713:ℚ)/10000000000),((3466261341:ℚ)/5000000000),((-21596352069:ℚ)/49600000000),((-4232282713:ℚ)/12637500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4881647387:ℚ)/10000000000),((555910593485927774875935369911710839235337:ℚ)/2078720458137600000000000000000000000000000),((1896416809637517085229786181:ℚ)/7393280000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6832704191:ℚ)/10000000000),((6992687431:ℚ)/10000000000),((-14578062293:ℚ)/33700000000),((-4352704191:ℚ)/12756250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2266120813:ℚ)/5000000000),((3297312814998634848255583950138397919365529608829236509834449:ℚ)/12455631249202578125000000000000000000000000000000000000000000),((1848935446172858602956616469:ℚ)/7393280000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6892891107:ℚ)/10000000000),((3526418663:ℚ)/5000000000),((-22137767967:ℚ)/51025000000),((-4412891107:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((869576023:ℚ)/2000000000),((1435269433087479590822019808914781708513658392559500570167:ℚ)/5420634708947656250000000000000000000000000000000000000000),((1824980284080971224433887101:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6953062743:ℚ)/10000000000),((444560799:ℚ)/625000000),((-2801047191:ℚ)/6437500000),((-4473062743:ℚ)/12993750000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2077969847:ℚ)/5000000000),((497043452316572998530748151190450355956116420974504489681:ℚ)/1876763280712366104125976562500000000000000000000000000000),((1800882050743754621981958501:ℚ)/7393280000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7013219529:ℚ)/10000000000),((112079597:ℚ)/156250000),((-236238791:ℚ)/541406250),((-4533219529:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3955311503:ℚ)/10000000000),((5108830115054239866648250562084211215467150315195493:ℚ)/19285136820673942565917968750000000000000000000000000),((1776640685964812788088531109:ℚ)/7393280000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((176834047:ℚ)/250000000),((113018781:ℚ)/156250000),((-717169029:ℚ)/1639062500),((-114834047:ℚ)/330781250),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((46807419:ℚ)/125000000),((89544719950668132010161345558627727453550750701197072141:ℚ)/337921178837094306945800781250000000000000000000000000000),((1095160082098955567336341:ℚ)/4620800000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((7133490193:ℚ)/10000000000),((3646648243:ℚ)/5000000000),((-23219834187:ℚ)/52925000000),((-4653490193:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((352196911:ℚ)/1000000000),((3354104996784270318777316051575551902878099528056317229499:ℚ)/12653615603208007812500000000000000000000000000000000000000),((1727728331764897342370805301:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((3596802427:ℚ)/5000000000),((7353378073:ℚ)/10000000000),((-15660134219:ℚ)/35600000000),((-2356802427:ℚ)/6734375000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((102656627:ℚ)/312500000),((8333866523241372738174233044415298479012719771025126144582989:ℚ)/31429379138160000000000000000000000000000000000000000000000000),((425764308148834001746638221:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7253706231:ℚ)/10000000000),((1853361773:ℚ)/2500000000),((-11880255957:ℚ)/26937500000),((-4773706231:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3030355243:ℚ)/10000000000),((7657929717236806058298061396702208849949632354293211616557961:ℚ)/28869613102074890136718750000000000000000000000000000000000000),((1678242782867906988230711589:ℚ)/7393280000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((3656897341:ℚ)/5000000000),((470846797:ℚ)/625000000),((-3037621173:ℚ)/6793750000),((-2416897341:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2753084049:ℚ)/10000000000),((2006550263441477562884479282075280822678903159920750816089:ℚ)/7491503336084880828857421875000000000000000000000000000000),((413321233025123950106420669:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((929241771:ℚ)/1250000000),((7773615197:ℚ)/10000000000),((-50762536773:ℚ)/110600000000),((-619241771:ℚ)/1787500000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2094316613:ℚ)/10000000000),((14811126575899645242737738313311730921726386155170500638077:ℚ)/54288524290000000000000000000000000000000000000000000000000),((25045919331254497565566509:ℚ)/115520000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((61392579:ℚ)/80000000),((8732355711:ℚ)/10000000000),((-59391201399:ℚ)/114400000000),((-41552579:ℚ)/129600000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((199837672770717201908421866455553:ℚ)/667180800000000000000000000000000),((21223931:ℚ)/102400000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((8633056701:ℚ)/10000000000),((2128961297:ℚ)/2000000000),((-5106883891:ℚ)/8640000000),((-6153056701:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1478526769460397440928287606771773237:ℚ)/4500000000000000000000000000000000000),((21223931:ℚ)/102400000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((2109170681:ℚ)/2000000000),((7229682101:ℚ)/5000000000),((-55467138909:ℚ)/80000000000),((-1613170681:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1966651928007897471140621:ℚ)/5078400000000000000000000),((21223931:ℚ)/102400000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC08
#check @N11Formalization.C450Source32GroupedC08.bound
#print axioms N11Formalization.C450Source32GroupedC08.valid0
#print axioms N11Formalization.C450Source32GroupedC08.valid1
#print axioms N11Formalization.C450Source32GroupedC08.valid2
#print axioms N11Formalization.C450Source32GroupedC08.valid3
#print axioms N11Formalization.C450Source32GroupedC08.valid4
#print axioms N11Formalization.C450Source32GroupedC08.valid5
#print axioms N11Formalization.C450Source32GroupedC08.valid6
#print axioms N11Formalization.C450Source32GroupedC08.valid7
#print axioms N11Formalization.C450Source32GroupedC08.valid8
#print axioms N11Formalization.C450Source32GroupedC08.valid9
#print axioms N11Formalization.C450Source32GroupedC08.valid10
#print axioms N11Formalization.C450Source32GroupedC08.valid11
#print axioms N11Formalization.C450Source32GroupedC08.valid12
#print axioms N11Formalization.C450Source32GroupedC08.valid13
#print axioms N11Formalization.C450Source32GroupedC08.bound
#print axioms N11Formalization.C450Source32GroupedC08.endpoint_checks
