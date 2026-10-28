import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1621095607:ℚ)/2500000000),((6701696181:ℚ)/10000000000),((-9545088543:ℚ)/49600000000),((-533095607:ℚ)/5055000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2743452843:ℚ)/5000000000),((18836069687148446644641718517292529857:ℚ)/152529920000000000000000000000000000000),((626175182151151746245937:ℚ)/11552000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((3302794759:ℚ)/5000000000),((6822836627:ℚ)/10000000000),((-3302836627:ℚ)/16850000000),((-1126794759:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2586510877:ℚ)/5000000000),((234377625842200242431290163795164922603654762739981523:ℚ)/1868786767578125000000000000000000000000000000000000000),((2156830353443707540135953:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6726703233:ℚ)/10000000000),((688337311:ℚ)/1000000000),((-1009011933:ℚ)/5150000000),((-339243319:ℚ)/2970000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1210258851:ℚ)/2500000000),((415054218338405709527739887439833469070467645260013:ℚ)/3334738159179687500000000000000000000000000000000000),((7223379723480606114021857:ℚ)/184832000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3393613369:ℚ)/5000000000),((1388777589:ℚ)/2000000000),((-684777589:ℚ)/3465000000),((-1217613369:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4667040139:ℚ)/10000000000),((1742555141877785007524015899081685011831525982659:ℚ)/13896093750000000000000000000000000000000000000000),((1629181655171388864654993:ℚ)/46208000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1711932211:ℚ)/2500000000),((7004381739:ℚ)/10000000000),((-10453145217:ℚ)/52450000000),((-623932211:ℚ)/5292500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((560860141:ℚ)/1250000000),((113913454434598948637226216368053580919868225702950652017:ℚ)/901813007031250000000000000000000000000000000000000000000),((362934196652016918497673:ℚ)/11552000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((138164203:ℚ)/200000000),((6869747:ℚ)/9765625),((-164747856:ℚ)/826953125),((-51124203:ℚ)/425300000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((34398221:ℚ)/80000000),((27804825864029172852033570266237559614150915104689:ℚ)/220903558959253132343292236328125000000000000000000),((2037615122086614257817:ℚ)/73932800000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((433652699:ℚ)/625000000),((7064855073:ℚ)/10000000000),((-10634565219:ℚ)/53162500000),((-53884233:ℚ)/445000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((4203331349:ℚ)/10000000000),((7414007155109662698478041926074588750526616481389777051:ℚ)/58691636869049072265625000000000000000000000000000000000),((18501595228725837778713:ℚ)/722000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((6805343:ℚ)/9765625),((7125308509:ℚ)/10000000000),((-3605308509:ℚ)/17800000000),((-20442744:ℚ)/168359375),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2052386963:ℚ)/5000000000),((4515316606014095511513556104061306899911046199033810029:ℚ)/35248450000000000000000000000000000000000000000000000000),((16700726469839715273:ℚ)/705078125000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3514556321:ℚ)/5000000000),((1796435647:ℚ)/2500000000),((-2749306941:ℚ)/13468750000),((-1338556321:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3900679017:ℚ)/10000000000),((1969442451143880865787927598937196981242599896252442789:ℚ)/15270803642272949218750000000000000000000000000000000000),((914704062302049274310433:ℚ)/46208000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7089534917:ℚ)/10000000000),((7246157829:ℚ)/10000000000),((-11178473487:ℚ)/54350000000),((-912511639:ℚ)/7310000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1842988229:ℚ)/5000000000),((8141491424361005307349847296395549053246827285955768847:ℚ)/62713159326171875000000000000000000000000000000000000000),((2936497688584891723041657:ℚ)/184832000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((714993857:ℚ)/1000000000),((456659671:ℚ)/625000000),((-236659671:ℚ)/1142187500),((-39970551:ℚ)/316000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((432335563:ℚ)/1250000000),((28298741138694076484391242922391973954590445051817:ℚ)/216582703590393066406250000000000000000000000000000),((22110365809077743939937:ℚ)/1848320000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((3605162049:ℚ)/5000000000),((1856823867:ℚ)/2500000000),((-2930471601:ℚ)/13825000000),((-1429162049:ℚ)/11250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((321612787:ℚ)/1000000000),((316160325870984095227650460474605515196873373843716567:ℚ)/2359268652343750000000000000000000000000000000000000000),((1026613592427871794233:ℚ)/128000000000000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((7331042677:ℚ)/10000000000),((7547968459:ℚ)/10000000000),((-1342656153:ℚ)/6250000000),((-229157129:ℚ)/1760000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2668327029:ℚ)/10000000000),((206848422857083041940224167696430338782156733858816073:ℚ)/1525878906250000000000000000000000000000000000000000000),((15769528835779968940377:ℚ)/184832000000000000000000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((7451694287:ℚ)/10000000000),((8030048207:ℚ)/10000000000),((-13530144621:ℚ)/57200000000),((-3099694287:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1978772723:ℚ)/10000000000),((44259009152716600882447316772260324484862522428959029101:ℚ)/292420700000000000000000000000000000000000000000000000000),((-1463504973576092122247103:ℚ)/184832000000000000000000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((991711933:ℚ)/1250000000),((170225623:ℚ)/200000000),((-299476869:ℚ)/1220000000),((-149237311:ℚ)/1080000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((442104561096718252071863428625837152301730841491429:ℚ)/2837262500000000000000000000000000000000000000000000),((-1142739:ℚ)/64000000)⟩
theorem valid14 : Valid source35 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((1682971883:ℚ)/2000000000),((5215103327:ℚ)/5000000000),((-1151701109:ℚ)/3600000000),((-812571883:ℚ)/6400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1256230213768424572737998436647507869226718006631967:ℚ)/6075000000000000000000000000000000000000000000000000),((-1142739:ℚ)/64000000)⟩
theorem valid15 : Valid source35 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10333576363:ℚ)/10000000000),((14252288749:ℚ)/10000000000),((-32196866247:ℚ)/80000000000),((-5981576363:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((35547624158829408171117046583987497101:ℚ)/128000000000000000000000000000000000000),((-1142739:ℚ)/64000000)⟩
theorem valid16 : Valid source35 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source35 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((45:ℚ)/64) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC11
#check @N11Formalization.C450Source35GroupedC11.bound
#print axioms N11Formalization.C450Source35GroupedC11.valid0
#print axioms N11Formalization.C450Source35GroupedC11.valid1
#print axioms N11Formalization.C450Source35GroupedC11.valid2
#print axioms N11Formalization.C450Source35GroupedC11.valid3
#print axioms N11Formalization.C450Source35GroupedC11.valid4
#print axioms N11Formalization.C450Source35GroupedC11.valid5
#print axioms N11Formalization.C450Source35GroupedC11.valid6
#print axioms N11Formalization.C450Source35GroupedC11.valid7
#print axioms N11Formalization.C450Source35GroupedC11.valid8
#print axioms N11Formalization.C450Source35GroupedC11.valid9
#print axioms N11Formalization.C450Source35GroupedC11.valid10
#print axioms N11Formalization.C450Source35GroupedC11.valid11
#print axioms N11Formalization.C450Source35GroupedC11.valid12
#print axioms N11Formalization.C450Source35GroupedC11.valid13
#print axioms N11Formalization.C450Source35GroupedC11.valid14
#print axioms N11Formalization.C450Source35GroupedC11.valid15
#print axioms N11Formalization.C450Source35GroupedC11.valid16
#print axioms N11Formalization.C450Source35GroupedC11.bound
#print axioms N11Formalization.C450Source35GroupedC11.endpoint_checks
