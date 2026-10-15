import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((248458569:ℚ)/400000000),((1679497391:ℚ)/2500000000),((-799497391:ℚ)/12400000000),((58741431:ℚ)/3968000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6140903761:ℚ)/10000000000),((125553376666493248195130171219123:ℚ)/3123812761600000000000000000000000),((-925861566337351044413591:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((835973349:ℚ)/1250000000),((3418518817:ℚ)/5000000000),((-1658518817:ℚ)/26700000000),((41342217:ℚ)/4450000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((494993187:ℚ)/1000000000),((12863290957731834448560372723851152273031126942161421:ℚ)/330454218750000000000000000000000000000000000000000000),((-230316684228274883577341:ℚ)/6080000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((850854803:ℚ)/1250000000),((3478037713:ℚ)/5000000000),((-1718037713:ℚ)/27175000000),((109145197:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4609358539:ℚ)/10000000000),((22789123303354918262766079481770658735271408674813809:ℚ)/587935868682861328125000000000000000000000000000000000),((-4542852588776319244461159:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((1385175931:ℚ)/2000000000),((7015590633:ℚ)/10000000000),((-3495590633:ℚ)/55300000000),((150824069:ℚ)/22120000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4243660163:ℚ)/10000000000),((74494758887390568594409494620780085849062810803574117:ℚ)/1932712880000000000000000000000000000000000000000000000),((-18842007443534191613922679:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((6985396537:ℚ)/10000000000),((7075103463:ℚ)/10000000000),((-3555103463:ℚ)/55775000000),((694603463:ℚ)/111550000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2024635443:ℚ)/5000000000),((2902441302073109221184363582820272877917508455182775031:ℚ)/75438127656250000000000000000000000000000000000000000000),((-19175555963557820971803159:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((3522455507:ℚ)/5000000000),((7134613977:ℚ)/10000000000),((-3614613977:ℚ)/56250000000),((317544493:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((384564301:ℚ)/1000000000),((8544751339515985369071684925471248156794570727874630427:ℚ)/222473144531250000000000000000000000000000000000000000000),((-19509062037238937639552919:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((3552211573:ℚ)/5000000000),((7194122233:ℚ)/10000000000),((-3674122233:ℚ)/56725000000),((287788427:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((453902307:ℚ)/1250000000),((349944255253211829912219087567936217022477314222350653:ℚ)/9126274303906250000000000000000000000000000000000000000),((-19842526004259446478184279:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((3581966497:ℚ)/5000000000),((7253628287:ℚ)/10000000000),((-3733628287:ℚ)/57200000000),((19848731:ℚ)/4400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((425494133:ℚ)/1250000000),((39746132436424423679387866221590889612048641600718851:ℚ)/1038180000000000000000000000000000000000000000000000000),((-20175948209968740959185159:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7223440613:ℚ)/10000000000),((228535381:ℚ)/312500000),((-118535381:ℚ)/1802343750),((456559387:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3161073777:ℚ)/10000000000),((977852017480363318245446531503299166477078745402342119:ℚ)/25580059256250000000000000000000000000000000000000000000),((-80114566272715721336059:ℚ)/1805000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/8),((-1:ℚ)/16),((3641473029:ℚ)/5000000000),((3686317001:ℚ)/5000000000),((-1926317001:ℚ)/29075000000),((198526971:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2898653301:ℚ)/10000000000),((2345588522198488217468673532759091853815314971698173941:ℚ)/61446786992187500000000000000000000000000000000000000000),((-5210667145770932128569911:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7342449383:ℚ)/10000000000),((929016721:ℚ)/1250000000),((-489016721:ℚ)/7328125000),((337550617:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2610800261:ℚ)/10000000000),((19202296656559816547181124705791310224254728707242489303:ℚ)/503719282226562500000000000000000000000000000000000000000),((-330874490116786354774651:ℚ)/7220000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7401936417:ℚ)/10000000000),((3775563679:ℚ)/5000000000),((-2015563679:ℚ)/29550000000),((92687861:ℚ)/39400000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2288011673:ℚ)/10000000000),((2915507027740127705886230761804375735183025378619428179:ℚ)/76453730000000000000000000000000000000000000000000000000),((-5376371376522102837497351:ℚ)/115520000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((3760446721:ℚ)/5000000000),((7670113339:ℚ)/10000000000),((-4150113339:ℚ)/60050000000),((79553279:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1444082061:ℚ)/10000000000),((10297374468824944475703504112151038848185439645756682481:ℚ)/270675562656250000000000000000000000000000000000000000000),((-5835783720436577:ℚ)/121600000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((3819922001:ℚ)/5000000000),((8145987883:ℚ)/10000000000),((-4625987883:ℚ)/61000000000),((20077999:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2718350975734996299062173732159371277541356534267457641:ℚ)/70931562500000000000000000000000000000000000000000000000),((-6267:ℚ)/128000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((4057793651:ℚ)/5000000000),((2009730713:ℚ)/2000000000),((-435243571:ℚ)/4320000000),((-217793651:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((681663449680171918919617498447118876460351250074175133833:ℚ)/17280000000000000000000000000000000000000000000000000000000),((-6267:ℚ)/128000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((10017853157:ℚ)/10000000000),((13851780163:ℚ)/10000000000),((-10331780163:ℚ)/80000000000),((-2337853157:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((437522227017168893500355849072108964709154349126539115871:ℚ)/10091796480000000000000000000000000000000000000000000000000),((-6267:ℚ)/128000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC15
#check @N11Formalization.C450Source13GroupedC15.bound
#print axioms N11Formalization.C450Source13GroupedC15.valid0
#print axioms N11Formalization.C450Source13GroupedC15.valid1
#print axioms N11Formalization.C450Source13GroupedC15.valid2
#print axioms N11Formalization.C450Source13GroupedC15.valid3
#print axioms N11Formalization.C450Source13GroupedC15.valid4
#print axioms N11Formalization.C450Source13GroupedC15.valid5
#print axioms N11Formalization.C450Source13GroupedC15.valid6
#print axioms N11Formalization.C450Source13GroupedC15.valid7
#print axioms N11Formalization.C450Source13GroupedC15.valid8
#print axioms N11Formalization.C450Source13GroupedC15.valid9
#print axioms N11Formalization.C450Source13GroupedC15.valid10
#print axioms N11Formalization.C450Source13GroupedC15.valid11
#print axioms N11Formalization.C450Source13GroupedC15.valid12
#print axioms N11Formalization.C450Source13GroupedC15.valid13
#print axioms N11Formalization.C450Source13GroupedC15.valid14
#print axioms N11Formalization.C450Source13GroupedC15.valid15
#print axioms N11Formalization.C450Source13GroupedC15.bound
#print axioms N11Formalization.C450Source13GroupedC15.endpoint_checks
