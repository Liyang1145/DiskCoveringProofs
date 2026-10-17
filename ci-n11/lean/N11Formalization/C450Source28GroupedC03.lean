import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7015285647:ℚ)/10000000000),((7182499533:ℚ)/10000000000),((-41957496731:ℚ)/49600000000),((-73918713411:ℚ)/100150000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((1974124881:ℚ)/5000000000),((1732631525988922282800697183501581905727465907456423804770169:ℚ)/4895611294474240000000000000000000000000000000000000000000000),((1526994776064067526595015047:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7074943849:ℚ)/10000000000),((7242080799:ℚ)/10000000000),((-42374565593:ℚ)/50075000000),((-74694270037:ℚ)/101100000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((747779709:ℚ)/2000000000),((94632600621540613889232528555547609108682301708356113066241969:ℚ)/267376939392293847656250000000000000000000000000000000000000000),((1530294333155106341197594223:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7134596691:ℚ)/10000000000),((3635934989:ℚ)/5000000000),((-7097181641:ℚ)/8425000000),((-75469756983:ℚ)/101575000000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((70354923:ℚ)/200000000),((5394719586428412231077517196228932371284936926440719500550771:ℚ)/15424937013394946289062500000000000000000000000000000000000000),((382986134933657171145003783:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7164421149:ℚ)/10000000000),((3650829103:ℚ)/5000000000),((-21395803721:ℚ)/25393750000),((-75857474937:ℚ)/102050000000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((850507163:ℚ)/2500000000),((551472219983276024673300762240819767402906894085989065731:ℚ)/1576666566830161094665527343750000000000000000000000000000),((383398758160483710231365007:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1798561081:ℚ)/2500000000),((916430687:ℚ)/1250000000),((-5375014809:ℚ)/6378125000),((-19061294053:ℚ)/25631250000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((3282403057:ℚ)/10000000000),((265006979651881785973046938290443146394939401173330512894899:ℚ)/757593315943172883987426757812500000000000000000000000000000),((23988215821329319697794287:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((7224066233:ℚ)/10000000000),((368061593:ℚ)/500000000),((-720143717:ℚ)/854375000),((-76632861029:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((394803087:ℚ)/1250000000),((43398927518089905836851525745940321566775939475248169289:ℚ)/124057012154695129394531250000000000000000000000000000000),((3842242200343154930004927:ℚ)/4620800000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3626943447:ℚ)/5000000000),((230969291:ℚ)/312500000),((-1356785037:ℚ)/1609375000),((-38510264811:ℚ)/51737500000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((3029558561:ℚ)/10000000000),((1561478196485556375856624252829262706696627402553765000487:ℚ)/4463161707488775253295898437500000000000000000000000000000),((1502488511819474408052663:ℚ)/1805000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1820926581:ℚ)/2500000000),((1484160373:ℚ)/2000000000),((-8725122611:ℚ)/10347500000),((-6450681851:ℚ)/8662500000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((1447575677:ℚ)/5000000000),((1539072414908913486615243385995259261123119406119259864669:ℚ)/4398767385006811523437500000000000000000000000000000000000),((61607995246101831634118967:ℚ)/73932800000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7313524541:ℚ)/10000000000),((7480368321:ℚ)/10000000000),((-44042578247:ℚ)/51975000000),((-77795819033:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1377195647:ℚ)/5000000000),((85451941358224142851945419014920558412197541517386492838876133:ℚ)/241409577745474584960937500000000000000000000000000000000000000),((1543504040986801351245088943:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7373157399:ℚ)/10000000000),((1884982831:ℚ)/2500000000),((-11114879817:ℚ)/13112500000),((-78571046187:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1224691491:ℚ)/5000000000),((22353920441279833748237943385826005492604456377520785257790923:ℚ)/63150709901076184082031250000000000000000000000000000000000000),((96675585295384009930965903:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((4645491:ℚ)/6250000),((7599490967:ℚ)/10000000000),((-44876436769:ℚ)/52925000000),((-16530461:ℚ)/22250000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((52539333:ℚ)/250000000),((8896957484986396276523414856546062319680632569788211959987:ℚ)/25133894006372070312500000000000000000000000000000000000000),((1550115857298860776097686047:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((7492409267:ℚ)/10000000000),((3918848839:ℚ)/5000000000),((-23271941873:ℚ)/26700000000),((-80121320471:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((168464857:ℚ)/1000000000),((5882250104654608071271130556466846572556363292594495588917967:ℚ)/15591477730893750000000000000000000000000000000000000000000000),((107350701:ℚ)/128000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((1932715241:ℚ)/2500000000),((2018964311:ℚ)/2500000000),((-12052750177:ℚ)/13825000000),((-20805298133:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((18155440785346195041147199140708040573997574210684685254349:ℚ)/48244684671777343750000000000000000000000000000000000000000),((107350701:ℚ)/128000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((7969249081:ℚ)/10000000000),((2257026847:ℚ)/2500000000),((-13719187929:ℚ)/14300000000),((-86320238053:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1535478468284796890643650986758669147579138528155295211411:ℚ)/3330854535937500000000000000000000000000000000000000000000),((107350701:ℚ)/128000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((4461139157:ℚ)/5000000000),((5465660949:ℚ)/5000000000),(-1:ℚ),((-49354809041:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((757802261471003989222062342386461481:ℚ)/1500000000000000000000000000000000000),((107350701:ℚ)/128000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((10826604327:ℚ)/10000000000),((7367545777:ℚ)/5000000000),(-1:ℚ),((-41155285417:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((90222090491502831660240753:ℚ)/169280000000000000000000000),((107350701:ℚ)/128000000)⟩
theorem valid15 : Valid source28 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC03
#check @N11Formalization.C450Source28GroupedC03.bound
#print axioms N11Formalization.C450Source28GroupedC03.valid0
#print axioms N11Formalization.C450Source28GroupedC03.valid1
#print axioms N11Formalization.C450Source28GroupedC03.valid2
#print axioms N11Formalization.C450Source28GroupedC03.valid3
#print axioms N11Formalization.C450Source28GroupedC03.valid4
#print axioms N11Formalization.C450Source28GroupedC03.valid5
#print axioms N11Formalization.C450Source28GroupedC03.valid6
#print axioms N11Formalization.C450Source28GroupedC03.valid7
#print axioms N11Formalization.C450Source28GroupedC03.valid8
#print axioms N11Formalization.C450Source28GroupedC03.valid9
#print axioms N11Formalization.C450Source28GroupedC03.valid10
#print axioms N11Formalization.C450Source28GroupedC03.valid11
#print axioms N11Formalization.C450Source28GroupedC03.valid12
#print axioms N11Formalization.C450Source28GroupedC03.valid13
#print axioms N11Formalization.C450Source28GroupedC03.valid14
#print axioms N11Formalization.C450Source28GroupedC03.valid15
#print axioms N11Formalization.C450Source28GroupedC03.bound
#print axioms N11Formalization.C450Source28GroupedC03.endpoint_checks
