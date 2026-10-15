import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6313345899:ℚ)/10000000000),((1647391169:ℚ)/2500000000),((-4142173507:ℚ)/12400000000),((-4905345899:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2952131673:ℚ)/5000000000),((3813819056567828143215668724491586138759581582105347187:ℚ)/105857928125000000000000000000000000000000000000000000000),((1745742973470307823969259:ℚ)/23104000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((3275638311:ℚ)/5000000000),((34137629:ℚ)/50000000),((-86412887:ℚ)/257500000),((-2571638311:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((33223401:ℚ)/62500000),((48771585443813453883257022951370762674458904162187351:ℚ)/1361471381250000000000000000000000000000000000000000000),((682721055312785695779:ℚ)/9241600000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((848647077:ℚ)/1250000000),((3473247119:ℚ)/5000000000),((-8819741357:ℚ)/26700000000),((-672647077:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((145666713:ℚ)/312500000),((73346425926208631347004000210140903336259066623901993:ℚ)/2093051692510986328125000000000000000000000000000000000),((6668121580368212435587659:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((69081161:ℚ)/100000000),((700597561:ℚ)/1000000000),((-1781792683:ℚ)/5435000000),((-55001161:ℚ)/219300000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1075018621:ℚ)/2500000000),((1437944691226019510346094995185032751188096224483:ℚ)/41465004640332031250000000000000000000000000000000),((263544282690561622826299:ℚ)/3696640000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((3483791687:ℚ)/5000000000),((7065455151:ℚ)/10000000000),((-17996365453:ℚ)/54825000000),((-2779791687:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((164334379:ℚ)/400000000),((627483323187097196611106596729991415219663965463385913:ℚ)/18108566541064453125000000000000000000000000000000000000),((26199043262587706538311819:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7027049059:ℚ)/10000000000),((3562466453:ℚ)/5000000000),((-9087399359:ℚ)/27650000000),((-5619049059:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1953906739:ℚ)/5000000000),((5191014822151375902968133258615880300642704182753808629:ℚ)/149921491509350585937500000000000000000000000000000000000),((6510930841591455448020371:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((1771628299:ℚ)/2500000000),((7184408921:ℚ)/10000000000),((-797966381:ℚ)/2425000000),((-473209433:ℚ)/1875000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1848497807:ℚ)/5000000000),((11252402629413225227585363803845904660937538729589:ℚ)/325217843055725097656250000000000000000000000000000),((25888468468489414687773179:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((446623489:ℚ)/625000000),((721414629:ℚ)/1000000000),((-1844243887:ℚ)/5625000000),((-358623489:ℚ)/1412187500),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1737016071:ℚ)/5000000000),((340911739723801967862781270015412872888378938430187:ℚ)/9901013055217266082763671875000000000000000000000000),((13541880436535815803041:ℚ)/194560000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1435141317:ℚ)/2000000000),((181097081:ℚ)/250000000),((-463291243:ℚ)/1412187500),((-1153541317:ℚ)/4538000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((839310867:ℚ)/2500000000),((14195818280534937090101987014426652066395264836214549:ℚ)/412416335793523437500000000000000000000000000000000000),((16032491833854329765259:ℚ)/231040000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((3602718491:ℚ)/5000000000),((3651677953:ℚ)/5000000000),((-9355033859:ℚ)/28362500000),((-2898718491:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3236409323:ℚ)/10000000000),((45850493481607427372696083951922951014843111266772641337:ℚ)/1327005136600000000000000000000000000000000000000000000000),((6394538310463416542931371:ℚ)/92416000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1452979341:ℚ)/2000000000),((7362826959:ℚ)/10000000000),((-18888480877:ℚ)/57200000000),((-1171379341:ℚ)/4614000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1490309179:ℚ)/5000000000),((2466927490862871300931797909184352896941850263607:ℚ)/71444306125854492187500000000000000000000000000000),((25423092710949424380622539:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((732435503:ℚ)/1000000000),((7422296439:ℚ)/10000000000),((-19066889317:ℚ)/57675000000),((-591635503:ℚ)/2326000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2701498159:ℚ)/10000000000),((391339660102185816168255056746709081836379506925041603:ℚ)/11340619007278125000000000000000000000000000000000000000),((69994727891251563833059:ℚ)/1024000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7383811991:ℚ)/10000000000),((471326927:ℚ)/625000000),((-1213980781:ℚ)/3634375000),((-5975811991:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2390886181:ℚ)/10000000000),((1931544762502606172668352669285303208416213574512344897:ℚ)/55572304993750000000000000000000000000000000000000000000),((98128379797098911820151:ℚ)/1444000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((7502721953:ℚ)/10000000000),((155581647:ℚ)/200000000),((-402744941:ℚ)/1182000000),((-6094721953:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1601695491:ℚ)/10000000000),((1936914378535640789238382700123442795421979638335759421:ℚ)/54977775000000000000000000000000000000000000000000000000),((16318029206680091:ℚ)/243200000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((77405269:ℚ)/100000000),((4127361711:ℚ)/5000000000),((-10782085133:ℚ)/30500000000),((-7036141:ℚ)/28800000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((760805411532027261616285941482201404277196709:ℚ)/21081600000000000000000000000000000000000000000),((8496337:ℚ)/128000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((2054020763:ℚ)/2500000000),((1015667779:ℚ)/1000000000),((-2727003337:ℚ)/6480000000),((-1702020763:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((658205534003254325775863420619293808612268346305290301:ℚ)/16200000000000000000000000000000000000000000000000000000),((8496337:ℚ)/128000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((126472233:ℚ)/125000000),((6979485303:ℚ)/5000000000),((-19338455909:ℚ)/40000000000),((-108872233:ℚ)/552000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((252212481540597573449680197092893442839319073557:ℚ)/5475150000000000000000000000000000000000000000000),((8496337:ℚ)/128000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC11
#check @N11Formalization.C450Source12GroupedC11.bound
#print axioms N11Formalization.C450Source12GroupedC11.valid0
#print axioms N11Formalization.C450Source12GroupedC11.valid1
#print axioms N11Formalization.C450Source12GroupedC11.valid2
#print axioms N11Formalization.C450Source12GroupedC11.valid3
#print axioms N11Formalization.C450Source12GroupedC11.valid4
#print axioms N11Formalization.C450Source12GroupedC11.valid5
#print axioms N11Formalization.C450Source12GroupedC11.valid6
#print axioms N11Formalization.C450Source12GroupedC11.valid7
#print axioms N11Formalization.C450Source12GroupedC11.valid8
#print axioms N11Formalization.C450Source12GroupedC11.valid9
#print axioms N11Formalization.C450Source12GroupedC11.valid10
#print axioms N11Formalization.C450Source12GroupedC11.valid11
#print axioms N11Formalization.C450Source12GroupedC11.valid12
#print axioms N11Formalization.C450Source12GroupedC11.valid13
#print axioms N11Formalization.C450Source12GroupedC11.valid14
#print axioms N11Formalization.C450Source12GroupedC11.valid15
#print axioms N11Formalization.C450Source12GroupedC11.valid16
#print axioms N11Formalization.C450Source12GroupedC11.bound
#print axioms N11Formalization.C450Source12GroupedC11.endpoint_checks
