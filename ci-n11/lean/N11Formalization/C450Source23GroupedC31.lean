import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((67092911:ℚ)/125000000),((2963800423:ℚ)/5000000000),((553650377:ℚ)/667500000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7866215769:ℚ)/10000000000),((-825972044577944217705186922823443:ℚ)/3098008300781250000000000000000000),((-23163370460491735989801:ℚ)/72200000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((5842971953:ℚ)/10000000000),((6165527609:ℚ)/10000000000),((6802971953:ℚ)/7900000000),((21312582827:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((433634297:ℚ)/625000000),((-228991148631537689396629507114391623600376469082106609:ℚ)/770373437500000000000000000000000000000000000000000000),((-72287252253070214894715177:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((95011151:ℚ)/156250000),((785560019:ℚ)/1250000000),((770078057:ℚ)/878906250),((2708680057:ℚ)/2765000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3216722937:ℚ)/5000000000),((-646037490801238402709156542794247389064390408307:ℚ)/2071942617476452142000198364257812500000000000000),((-139398199012324104727699:ℚ)/451250000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((1549894597:ℚ)/2500000000),((6403425949:ℚ)/10000000000),((12529262179:ℚ)/14300000000),((22026277847:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((770999137:ℚ)/1250000000),((-129364341834196833582886193799171895920668467997006617:ℚ)/415370312500000000000000000000000000000000000000000000),((-4402364357852445810492277:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1263687859:ℚ)/2000000000),((807862053:ℚ)/1250000000),((10189815013:ℚ)/11535000000),((2775586159:ℚ)/2860000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2946107167:ℚ)/5000000000),((-29830550856598824203472965265545190301766616278189:ℚ)/93676974815368652343750000000000000000000000000000),((-2799245981993037119524593:ℚ)/9241600000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6377868377:ℚ)/10000000000),((1304473067:ℚ)/2000000000),((51365078639:ℚ)/58150000000),((4476619201:ℚ)/4614000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((8984349:ℚ)/15625000),((-97762832772870250836402511295691032420412245083989756583:ℚ)/307233934960937500000000000000000000000000000000000000000),((-3658657558995762400731523:ℚ)/12160000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((3218648287:ℚ)/5000000000),((82272909:ℚ)/125000000),((3698648287:ℚ)/4187500000),((282018727:ℚ)/290750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1401140447:ℚ)/2500000000),((-36481836766156983808426958933086852377891810540017671:ℚ)/114731979370117187500000000000000000000000000000000000),((-17261986494861272125427657:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1624180977:ℚ)/2500000000),((6641298617:ℚ)/10000000000),((4349755613:ℚ)/4925000000),((22739895851:ℚ)/23450000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5455691531:ℚ)/10000000000),((-14827561029713392712317327969906241776205381701720981:ℚ)/46663653564453125000000000000000000000000000000000000),((-12859032435045641897267911:ℚ)/43320000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6556150399:ℚ)/10000000000),((6700763061:ℚ)/10000000000),((52613052793:ℚ)/59575000000),((22918289183:ℚ)/23640000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5303079153:ℚ)/10000000000),((-104909016127881500405206314821652584002846257096590608249:ℚ)/330378805834960937500000000000000000000000000000000000000),((-68115174362000101531364553:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1653894017:ℚ)/2500000000),((6760226087:ℚ)/10000000000),((13257258119:ℚ)/15012500000),((23096678261:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((514638869:ℚ)/1000000000),((-419411180219459545571648210407384881070204225161616367:ℚ)/1321658020782470703125000000000000000000000000000000000),((-4228059363981905983094917:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1335000187:ℚ)/2000000000),((6819687729:ℚ)/10000000000),((10689001309:ℚ)/12105000000),((23275063187:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((311577031:ℚ)/625000000),((-219738400065578533565964959814899872220528795542671077:ℚ)/692874241259765625000000000000000000000000000000000000),((-2687313297293761812599457:ℚ)/9241600000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((3367212509:ℚ)/5000000000),((3439574009:ℚ)/5000000000),((26930487563:ℚ)/30500000000),((11726722027:ℚ)/12105000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((602394923:ℚ)/1250000000),((-14051148867243575823633620770319826683932116496267717091:ℚ)/44332226562500000000000000000000000000000000000000000000),((-46202785276102796213513:ℚ)/160000000000000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((424615521:ℚ)/625000000),((3469303493:ℚ)/5000000000),((3392308647:ℚ)/3842187500),((11815910479:ℚ)/12200000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((2323819509:ℚ)/5000000000),((-1754602005636699568050775230403670271876740055707571:ℚ)/5539055384323000907897949218750000000000000000000000),((-1552755892636620824290013:ℚ)/5415000000000000000000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3426635453:ℚ)/5000000000),((874758083:ℚ)/1250000000),((3906635453:ℚ)/4425000000),((2976274249:ℚ)/3073750000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((2235020511:ℚ)/5000000000),((-14287023989574236693457513706627272068082935262244543:ℚ)/45127221679687500000000000000000000000000000000000000),((-16446280156149312368308177:ℚ)/57760000000000000000000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((3456346373:ℚ)/5000000000),((3558488133:ℚ)/5000000000),((27554424611:ℚ)/31450000000),((12083464399:ℚ)/12390000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1071401601:ℚ)/2500000000),((-221460033318031292391417248631575425829153363961402571:ℚ)/714781103515625000000000000000000000000000000000000000),((-853192197737066746698523:ℚ)/3040000000000000000000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((70315343:ℚ)/100000000),((1838696307:ℚ)/2500000000),((559407401:ℚ)/648000000),((6220088921:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3892290757:ℚ)/10000000000),((-1559896547320732046211292459696586123457511475153:ℚ)/5248800000000000000000000000000000000000000000000),((-6295798218909535833497:ℚ)/23104000000000000000000)⟩
theorem valid15 : Valid source23 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((7269209347:ℚ)/10000000000),((1661171729:ℚ)/2000000000),((57604465429:ℚ)/72400000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((185077141:ℚ)/625000000),((-8733715717209620484430197789486607615944781977036844597:ℚ)/37060881250000000000000000000000000000000000000000000000),((-61037686199237398869101777:ℚ)/231040000000000000000000000)⟩
theorem valid16 : Valid source23 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((4109908787:ℚ)/5000000000),((9256727831:ℚ)/10000000000),((32129361509:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-6060042459419809461269648633327087106373000657390848637:ℚ)/25000000000000000000000000000000000000000000000000000000),((-16926503:ℚ)/64000000)⟩
theorem valid17 : Valid source23 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source23 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((2292577537:ℚ)/2500000000),((13059006853:ℚ)/10000000000),((17728042759:ℚ)/27600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-47890825587045810311775032919104887:ℚ)/438012000000000000000000000000000000),((-16926503:ℚ)/64000000)⟩
theorem valid18 : Valid source23 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2383:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source23 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source23 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC31
#check @N11Formalization.C450Source23GroupedC31.bound
#print axioms N11Formalization.C450Source23GroupedC31.valid0
#print axioms N11Formalization.C450Source23GroupedC31.valid1
#print axioms N11Formalization.C450Source23GroupedC31.valid2
#print axioms N11Formalization.C450Source23GroupedC31.valid3
#print axioms N11Formalization.C450Source23GroupedC31.valid4
#print axioms N11Formalization.C450Source23GroupedC31.valid5
#print axioms N11Formalization.C450Source23GroupedC31.valid6
#print axioms N11Formalization.C450Source23GroupedC31.valid7
#print axioms N11Formalization.C450Source23GroupedC31.valid8
#print axioms N11Formalization.C450Source23GroupedC31.valid9
#print axioms N11Formalization.C450Source23GroupedC31.valid10
#print axioms N11Formalization.C450Source23GroupedC31.valid11
#print axioms N11Formalization.C450Source23GroupedC31.valid12
#print axioms N11Formalization.C450Source23GroupedC31.valid13
#print axioms N11Formalization.C450Source23GroupedC31.valid14
#print axioms N11Formalization.C450Source23GroupedC31.valid15
#print axioms N11Formalization.C450Source23GroupedC31.valid16
#print axioms N11Formalization.C450Source23GroupedC31.valid17
#print axioms N11Formalization.C450Source23GroupedC31.valid18
#print axioms N11Formalization.C450Source23GroupedC31.bound
#print axioms N11Formalization.C450Source23GroupedC31.endpoint_checks
