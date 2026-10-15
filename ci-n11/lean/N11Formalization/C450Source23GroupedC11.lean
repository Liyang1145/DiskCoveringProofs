import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((1602734833:ℚ)/2500000000),((3357800741:ℚ)/5000000000),((-6713402223:ℚ)/24800000000),((-898734833:ℚ)/5150000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5669468079:ℚ)/10000000000),((1249748108574810862566734581482972823845292442928138871:ℚ)/6616120507812500000000000000000000000000000000000000000),((-212201326717865903967177:ℚ)/23104000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6650356641:ℚ)/10000000000),((1708824731:ℚ)/2500000000),((-3446474193:ℚ)/12875000000),((-3834356641:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((78947433:ℚ)/156250000),((68679068188885290006902463827816869811388937186669296951:ℚ)/371546958896875000000000000000000000000000000000000000000),((-21975269253539307659538299:ℚ)/1108992000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((6770012603:ℚ)/10000000000),((6954962267:ℚ)/10000000000),((-14144886801:ℚ)/52450000000),((-1318004201:ℚ)/7120000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4717131197:ℚ)/10000000000),((27271615656320376685465922028725864936845446112169357817:ℚ)/147902496200000000000000000000000000000000000000000000000),((-9303119645941836892035137:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3444817987:ℚ)/5000000000),((7074593323:ℚ)/10000000000),((-4834593323:ℚ)/17800000000),((-2036817987:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4358037303:ℚ)/10000000000),((32858474233942569936682446207255611033163740459775629411:ℚ)/178607077760937500000000000000000000000000000000000000000),((-2822477819049109181655217:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7009228487:ℚ)/10000000000),((7134397277:ℚ)/10000000000),((-14683191831:ℚ)/54350000000),((-1397742829:ℚ)/7310000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((496114837:ℚ)/1250000000),((1777843516271978650368522548375204731244504020840116267:ℚ)/9756471680078125000000000000000000000000000000000000000),((-13285486026271354959816217:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((88362671:ℚ)/125000000),((7194193783:ℚ)/10000000000),((-4954193783:ℚ)/18275000000),((-53162671:ℚ)/276500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3760204387:ℚ)/10000000000),((68683602347623148537117208684879919113853479009357:ℚ)/377261802938842773437500000000000000000000000000000),((-2232277084880521595913:ℚ)/57760000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1425758351:ℚ)/2000000000),((3626991517:ℚ)/5000000000),((-7520974551:ℚ)/27650000000),((-37502537:ℚ)/194000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3539846969:ℚ)/10000000000),((71724634702532692378079087101649048370204826871073:ℚ)/394303257031250000000000000000000000000000000000000),((-611594552191955958037193:ℚ)/14786560000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((1437712579:ℚ)/2000000000),((228555163:ℚ)/312500000),((-475665489:ℚ)/1742968750),((-291504193:ℚ)/1500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3305513497:ℚ)/10000000000),((8352890834206067173415515967212590339112156950335791:ℚ)/45957183837890625000000000000000000000000000000000000),((-651814386539333356756913:ℚ)/14786560000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((7248327279:ℚ)/10000000000),((7433309091:ℚ)/10000000000),((-5193309091:ℚ)/18750000000),((-4432327279:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3053982889:ℚ)/10000000000),((84876779796888145769773845491713087511215983335134141:ℚ)/464006400000000000000000000000000000000000000000000000),((-51909189398445828169786139:ℚ)/1108992000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((368391823:ℚ)/500000000),((959039943:ℚ)/1250000000),((-2037119829:ℚ)/7150000000),((-75863941:ℚ)/394000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1239044837:ℚ)/5000000000),((632598458996109192858286033637093453397179201447619:ℚ)/3416526059375000000000000000000000000000000000000000),((-48312753258677946193097:ℚ)/924160000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((950847617:ℚ)/1250000000),((395561753:ℚ)/500000000),((-283561753:ℚ)/985000000),((-598847617:ℚ)/3050000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((1611860508326790265186214745969356883841097651848346133:ℚ)/8733448632812500000000000000000000000000000000000000000),((-8060847:ℚ)/128000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((245176083:ℚ)/312500000),((2097203763:ℚ)/2500000000),((-4611611289:ℚ)/15250000000),((-157176083:ℚ)/810000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1061541508205974660619926606372109982410559621558679:ℚ)/5628107812500000000000000000000000000000000000000000),((-8060847:ℚ)/128000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((83231021:ℚ)/100000000),((643541841:ℚ)/625000000),((-503541841:ℚ)/1350000000),((-55071021:ℚ)/320000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((291537827842549832144723724070785225713453232896111:ℚ)/1382400000000000000000000000000000000000000000000000),((-8060847:ℚ)/128000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((2557653619:ℚ)/2500000000),((14105866581:ℚ)/10000000000),((-35597599743:ℚ)/80000000000),((-1853653619:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((126140194843212545501850810851441343090962585972316427:ℚ)/525614400000000000000000000000000000000000000000000000),((-8060847:ℚ)/128000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source23 nn0 nn1 Qcell ((2231:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source23 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC11
#check @N11Formalization.C450Source23GroupedC11.bound
#print axioms N11Formalization.C450Source23GroupedC11.valid0
#print axioms N11Formalization.C450Source23GroupedC11.valid1
#print axioms N11Formalization.C450Source23GroupedC11.valid2
#print axioms N11Formalization.C450Source23GroupedC11.valid3
#print axioms N11Formalization.C450Source23GroupedC11.valid4
#print axioms N11Formalization.C450Source23GroupedC11.valid5
#print axioms N11Formalization.C450Source23GroupedC11.valid6
#print axioms N11Formalization.C450Source23GroupedC11.valid7
#print axioms N11Formalization.C450Source23GroupedC11.valid8
#print axioms N11Formalization.C450Source23GroupedC11.valid9
#print axioms N11Formalization.C450Source23GroupedC11.valid10
#print axioms N11Formalization.C450Source23GroupedC11.valid11
#print axioms N11Formalization.C450Source23GroupedC11.valid12
#print axioms N11Formalization.C450Source23GroupedC11.valid13
#print axioms N11Formalization.C450Source23GroupedC11.bound
#print axioms N11Formalization.C450Source23GroupedC11.endpoint_checks
