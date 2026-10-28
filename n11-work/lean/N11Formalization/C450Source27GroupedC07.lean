import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1676781043:ℚ)/2500000000),((6916378667:ℚ)/10000000000),((-5316378667:ℚ)/9920000000),((-10931029387:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4896099943:ℚ)/10000000000),((244883664281618776107194098335416483289415461763072289593:ℚ)/1042783016308593750000000000000000000000000000000000000000),((7284487459312708909710929:ℚ)/23104000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((3413461989:ℚ)/5000000000),((6976245217:ℚ)/10000000000),((-1792081739:ℚ)/3370000000),((-22401157901:ℚ)/51025000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4549580321:ℚ)/10000000000),((40444701264559757486986945429400343353426800127616666899:ℚ)/174879529319885253906250000000000000000000000000000000000),((86431814130364202517816323:ℚ)/277248000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((860851129:ℚ)/1250000000),((7036102589:ℚ)/10000000000),((-5436102589:ℚ)/10205000000),((-5667660161:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((109171011:ℚ)/250000000),((6304532430139363055016958822104562579447378794708103432647:ℚ)/27224802331542968750000000000000000000000000000000000000000),((1790353789455074621342361:ℚ)/5776000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((3473342279:ℚ)/5000000000),((7095951039:ℚ)/10000000000),((-5495951039:ℚ)/10300000000),((-22940080511:ℚ)/51975000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2088338919:ℚ)/5000000000),((1746445510340337233771263223728765951922823782373704460517:ℚ)/7532159187963867187500000000000000000000000000000000000000),((28479868422993670059345561:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7006550821:ℚ)/10000000000),((1425174399:ℚ)/2000000000),((-157882057:ℚ)/297000000),((-46418957389:ℚ)/104425000000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((248626457:ℚ)/625000000),((40544107512518361881266201501838034256826803132352698368577:ℚ)/176144331788745117187500000000000000000000000000000000000000),((113252911052271726853189761:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7036480559:ℚ)/10000000000),((1788947703:ℚ)/2500000000),((-1388947703:ℚ)/2610625000),((-46688325031:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3875104121:ℚ)/10000000000),((1735225173001571888852974039434310123060787577128195346519761:ℚ)/7533745860739062500000000000000000000000000000000000000000000),((112918356665307164028853001:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((7066408077:ℚ)/10000000000),((2806917:ℚ)/3906250),((-8727668:ℚ)/16390625),((-46957672693:ℚ)/105375000000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((3769529489:ℚ)/10000000000),((5893497042122654970098905006877667846361528566073116962497:ℚ)/25570958872192382812500000000000000000000000000000000000000),((337748860068268401581283827:ℚ)/1108992000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((3548166703:ℚ)/5000000000),((7215622147:ℚ)/10000000000),((-1871874049:ℚ)/3512500000),((-23613500327:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3661069061:ℚ)/10000000000),((60044277142897472915922759405559783201275946756598791994961:ℚ)/260356807348925781250000000000000000000000000000000000000000),((28061675242567658388084489:ℚ)/92416000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((3563128287:ℚ)/5000000000),((7245534721:ℚ)/10000000000),((-5645534721:ℚ)/10585000000),((-23748154583:ℚ)/53162500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1774728831:ℚ)/5000000000),((458766693184028971224268305588326736738174303934458885176613:ℚ)/1988003124028430175781250000000000000000000000000000000000000),((83932199537781905723767547:ℚ)/277248000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((7156177611:ℚ)/10000000000),((7275445271:ℚ)/10000000000),((-5675445271:ℚ)/10632500000),((-47765598499:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3434387437:ℚ)/10000000000),((623089498612612016762681858332810114769681940733206733443083:ℚ)/2698409841300000000000000000000000000000000000000000000000000),((334714945339085952202221923:ℚ)/1108992000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7186096547:ℚ)/10000000000),((7305353823:ℚ)/10000000000),((-5705353823:ℚ)/10680000000),((-48034868923:ℚ)/107275000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((207218599:ℚ)/625000000),((2479085292521056233157294644545625455399474243160043334741:ℚ)/10729651582670593261718750000000000000000000000000000000000),((111232848004669816827877489:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((7216013409:ℚ)/10000000000),((1833815101:ℚ)/2500000000),((-1433815101:ℚ)/2681875000),((-48304120681:ℚ)/107750000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1596180341:ℚ)/5000000000),((30298091164616908733056823839205934977692004080884345833877:ℚ)/131054036857986450195312500000000000000000000000000000000000),((332679593806984225456993403:ℚ)/1108992000000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3622964113:ℚ)/5000000000),((7395067761:ℚ)/10000000000),((-5795067761:ℚ)/10775000000),((-24286677017:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((766116019:ℚ)/2500000000),((100849415902227609524636977174964662248202578745336217440001:ℚ)/432469946713281250000000000000000000000000000000000000000000),((27638174522601780111386249:ℚ)/92416000000000000000000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7305751833:ℚ)/10000000000),((3757329977:ℚ)/5000000000),((-2957329977:ℚ)/5435000000),((-49111766497:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2791748867:ℚ)/10000000000),((34050892994237897307329140197650923834915335325978349547873:ℚ)/143613401405468750000000000000000000000000000000000000000000),((329607445650293685044599307:ℚ)/1108992000000000000000000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((742537567:ℚ)/1000000000),((7753759571:ℚ)/10000000000),((-6153759571:ℚ)/11060000000),((-5018838103:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((536952259:ℚ)/2500000000),((1265302736574758940816608868640784965236816065573378885777:ℚ)/5174676707200000000000000000000000000000000000000000000000),((1084918465350119446451369:ℚ)/3696640000000000000000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((7664535357:ℚ)/10000000000),((8709212123:ℚ)/10000000000),((-546862471:ℚ)/880000000),((-52340818213:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2657971046557781811421973343147465144370543480266210539:ℚ)/9314870400000000000000000000000000000000000000000000000),((1474463:ℚ)/5120000)⟩
theorem valid15 : Valid source27 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((8620192363:ℚ)/10000000000),((10616990521:ℚ)/10000000000),((-3005663507:ℚ)/4320000000),((-60941731267:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((55030669807571058875697114522633858942444791638361047:ℚ)/167961600000000000000000000000000000000000000000000000),((1474463:ℚ)/5120000)⟩
theorem valid16 : Valid source27 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((10528261697:ℚ)/10000000000),((1442609887:ℚ)/1000000000),((-1282609887:ℚ)/1600000000),((-78114355273:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((12289890951013435383836406779030431679226919061838212801:ℚ)/30470400000000000000000000000000000000000000000000000000),((1474463:ℚ)/5120000)⟩
theorem valid17 : Valid source27 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((4253:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source27 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source27 nn0 nn1 Qcell ((4253:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source27 nn0 nn1 Qcell ((4253:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC07
#check @N11Formalization.C450Source27GroupedC07.bound
#print axioms N11Formalization.C450Source27GroupedC07.valid0
#print axioms N11Formalization.C450Source27GroupedC07.valid1
#print axioms N11Formalization.C450Source27GroupedC07.valid2
#print axioms N11Formalization.C450Source27GroupedC07.valid3
#print axioms N11Formalization.C450Source27GroupedC07.valid4
#print axioms N11Formalization.C450Source27GroupedC07.valid5
#print axioms N11Formalization.C450Source27GroupedC07.valid6
#print axioms N11Formalization.C450Source27GroupedC07.valid7
#print axioms N11Formalization.C450Source27GroupedC07.valid8
#print axioms N11Formalization.C450Source27GroupedC07.valid9
#print axioms N11Formalization.C450Source27GroupedC07.valid10
#print axioms N11Formalization.C450Source27GroupedC07.valid11
#print axioms N11Formalization.C450Source27GroupedC07.valid12
#print axioms N11Formalization.C450Source27GroupedC07.valid13
#print axioms N11Formalization.C450Source27GroupedC07.valid14
#print axioms N11Formalization.C450Source27GroupedC07.valid15
#print axioms N11Formalization.C450Source27GroupedC07.valid16
#print axioms N11Formalization.C450Source27GroupedC07.valid17
#print axioms N11Formalization.C450Source27GroupedC07.bound
#print axioms N11Formalization.C450Source27GroupedC07.endpoint_checks
