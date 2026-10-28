import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1715545431:ℚ)/2500000000),((7098522041:ℚ)/10000000000),((-4922522041:ℚ)/9920000000),((-9839908879:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2221419931:ℚ)/5000000000),((5081455920636373447725273762767727817:ℚ)/15252992000000000000000000000000000000),((2238253490965748410934293:ℚ)/5776000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((6982895667:ℚ)/10000000000),((1431759381:ℚ)/2000000000),((-996559381:ℚ)/2022000000),((-40446061003:ℚ)/102050000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((405761561:ℚ)/1000000000),((531156466539750075259530874310857668440921540473981:ℚ)/1614631767187500000000000000000000000000000000000000),((35292889032713784469134157:ℚ)/92416000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((7043224549:ℚ)/10000000000),((3609527399:ℚ)/5000000000),((-2521527399:ℚ)/5102500000),((-40989020941:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((1925776833:ℚ)/5000000000),((420022577712176923552994439525255405276733477611747:ℚ)/1277367025390625000000000000000000000000000000000000),((35030645801204537895399613:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((887941927:ℚ)/1250000000),((3639648099:ℚ)/5000000000),((-2551648099:ℚ)/5150000000),((-5191477343:ℚ)/12993750000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((3634505561:ℚ)/10000000000),((548049551664221932158961437161623088753427323215611:ℚ)/1667369079589843750000000000000000000000000000000000),((543228570820653386089877:ℚ)/1444000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3581914389:ℚ)/5000000000),((7339521567:ℚ)/10000000000),((-5163521567:ℚ)/10395000000),((-21037229501:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3404363771:ℚ)/10000000000),((4992904459078261588994713877877649260924236962497113:ℚ)/15195378515625000000000000000000000000000000000000000),((8625209157562898248636573:ℚ)/23104000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((3612052563:ℚ)/5000000000),((7399731349:ℚ)/10000000000),((-5223731349:ℚ)/10490000000),((-21308473067:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3158259939:ℚ)/10000000000),((1184932743125004301584021099826910939242212425457426101:ℚ)/3607252028125000000000000000000000000000000000000000000),((8558317379876904923789197:ℚ)/23104000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((7284364931:ℚ)/10000000000),((745992597:ℚ)/1000000000),((-528392597:ℚ)/1058500000),((-43159284379:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2892114339:ℚ)/10000000000),((912846491884104286739228843722342029430714309743319:ℚ)/2779610042871093750000000000000000000000000000000000),((33963926654376121024101293:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((918076081:ℚ)/1250000000),((3790135683:ℚ)/5000000000),((-2702135683:ℚ)/5340000000),((-5462684729:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4159633:ℚ)/16000000),((23655196168528129687559579482742843:ℚ)/71289000000000000000000000000000000),((526450117233786433010693:ℚ)/1444000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((3732524777:ℚ)/5000000000),((7700560877:ℚ)/10000000000),((-5524560877:ℚ)/10870000000),((-22392722993:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((943648177:ℚ)/5000000000),((36740670482592327137471969177950453:ℚ)/110772093750000000000000000000000000),((8286309579265910084693077:ℚ)/23104000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7585431161:ℚ)/10000000000),((7940983657:ℚ)/10000000000),((-5764983657:ℚ)/11060000000),((-45868880449:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((619284309:ℚ)/10000000000),((14778859724387310432319685417853791:ℚ)/43687000000000000000000000000000000),((90278554283443491054893:ℚ)/256000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((1565205721:ℚ)/2000000000),((69538551:ℚ)/78125000),((-4041427:ℚ)/6875000),((-9606851489:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((267221591010325380955510781383:ℚ)/708984375000000000000000000000),((5630701:ℚ)/16000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((4393286237:ℚ)/5000000000),((10815101863:ℚ)/10000000000),((-959900207:ℚ)/1440000000),((-28339576133:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((724880343787267813666195999406099:ℚ)/1728000000000000000000000000000000),((5630701:ℚ)/16000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((668848759:ℚ)/625000000),((7315828741:ℚ)/5000000000),((-6227828741:ℚ)/8000000000),((-4619638831:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((8209972573261228614931813:ℚ)/16000000000000000000000000),((5630701:ℚ)/16000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC07
#check @N11Formalization.C450Source36GroupedC07.bound
#print axioms N11Formalization.C450Source36GroupedC07.valid0
#print axioms N11Formalization.C450Source36GroupedC07.valid1
#print axioms N11Formalization.C450Source36GroupedC07.valid2
#print axioms N11Formalization.C450Source36GroupedC07.valid3
#print axioms N11Formalization.C450Source36GroupedC07.valid4
#print axioms N11Formalization.C450Source36GroupedC07.valid5
#print axioms N11Formalization.C450Source36GroupedC07.valid6
#print axioms N11Formalization.C450Source36GroupedC07.valid7
#print axioms N11Formalization.C450Source36GroupedC07.valid8
#print axioms N11Formalization.C450Source36GroupedC07.valid9
#print axioms N11Formalization.C450Source36GroupedC07.valid10
#print axioms N11Formalization.C450Source36GroupedC07.valid11
#print axioms N11Formalization.C450Source36GroupedC07.valid12
#print axioms N11Formalization.C450Source36GroupedC07.bound
#print axioms N11Formalization.C450Source36GroupedC07.endpoint_checks
