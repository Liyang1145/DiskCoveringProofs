import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((133044491:ℚ)/200000000),((1718620803:ℚ)/2500000000),((-1078620803:ℚ)/3100000000),((-508911437:ℚ)/2022000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5047555731:ℚ)/10000000000),((17244376039002616687316425571035869:ℚ)/74477500000000000000000000000000000),((1108079760926420236927911:ℚ)/5914624000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((846629351:ℚ)/1250000000),((874398493:ℚ)/1250000000),((-554398493:ℚ)/1579687500),((-3286405457:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4708372639:ℚ)/10000000000),((357449533332991399680867678551528851388847703351241:ℚ)/1539832846820354461669921875000000000000000000000000),((41609841279442553962451631:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6893767143:ℚ)/10000000000),((220484777:ℚ)/312500000),((-140484777:ℚ)/402343750),((-9045456667:ℚ)/34650000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1086285693:ℚ)/2500000000),((182591563579948828824057027085163929026200045583:ℚ)/795063533587381243705749511718750000000000000000),((7664001920265601890139244557:ℚ)/44359680000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1738526367:ℚ)/2500000000),((1778955043:ℚ)/2500000000),((-379651681:ℚ)/1082812500),((-6889684569:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2076270043:ℚ)/5000000000),((7900532694346214267631452779218979928429620562563:ℚ)/34350085258483886718750000000000000000000000000000),((468757159760001738662382877:ℚ)/2772480000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((3507212963:ℚ)/5000000000),((1794027589:ℚ)/2500000000),((-1154027589:ℚ)/3278125000),((-13990490741:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3951189637:ℚ)/10000000000),((50714802047353793092249438507384820484444542885432133:ℚ)/220169191169738769531250000000000000000000000000000000),((611277562059727159524094039:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((7074729013:ℚ)/10000000000),((7236383887:ℚ)/10000000000),((-4676383887:ℚ)/13231250000),((-28403103091:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((467459053:ℚ)/1250000000),((834931113664803232379547490960191854412965991525915279:ℚ)/3619283909988403320312500000000000000000000000000000000),((2389883319631309673219372839:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((7135015207:ℚ)/10000000000),((7296641219:ℚ)/10000000000),((-4736641219:ℚ)/13350000000),((-28825106449:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3516147613:ℚ)/10000000000),((10306785586059329712470479825241501696218634812649797121:ℚ)/44611319531250000000000000000000000000000000000000000000),((2334357230073241923923823919:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((899410621:ℚ)/1250000000),((7356882789:ℚ)/10000000000),((-4796882789:ℚ)/13468750000),((-3655874347:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1639076501:ℚ)/5000000000),((3533383671407466723044600330414374127628733545565240933:ℚ)/15270803642272949218750000000000000000000000000000000000),((35602059636576335632645271:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7255538741:ℚ)/10000000000),((1495464063:ℚ)/2000000000),((-983464063:ℚ)/2717500000),((-29668771187:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3022264863:ℚ)/10000000000),((5516828374828919936261177700365398587429069623677157:ℚ)/23517434747314453125000000000000000000000000000000000),((2222406921151268753058223911:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((461000001:ℚ)/625000000),((1543604761:ℚ)/2000000000),((-1031604761:ℚ)/2765000000),((-173363637:ℚ)/650000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2433911009:ℚ)/10000000000),((4543905053178246562353308658719651802463204156809271:ℚ)/18874149218750000000000000000000000000000000000000000),((24717868179976165216163293:ℚ)/173280000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((7616748541:ℚ)/10000000000),((2169731903:ℚ)/2500000000),((-1529731903:ℚ)/3575000000),((-32197239787:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((58332063830680234464247688292190429608691791498115133:ℚ)/214175317382812500000000000000000000000000000000000000),((26253689:ℚ)/204800000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8577805183:ℚ)/10000000000),((1059444513:ℚ)/1000000000),((-803444513:ℚ)/1620000000),((-38924636281:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1520919851571779157707906682327688462903751437355467:ℚ)/4982259375000000000000000000000000000000000000000000),((26253689:ℚ)/204800000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((2098707829:ℚ)/2000000000),((14412570671:ℚ)/10000000000),((-11852570671:ℚ)/20000000000),((-10466954803:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((18597591057779176989071756427368997:ℚ)/50000000000000000000000000000000000),((26253689:ℚ)/204800000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source34 nn0 nn1 Qcell ((2079:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC09
#check @N11Formalization.C450Source34GroupedC09.bound
#print axioms N11Formalization.C450Source34GroupedC09.valid0
#print axioms N11Formalization.C450Source34GroupedC09.valid1
#print axioms N11Formalization.C450Source34GroupedC09.valid2
#print axioms N11Formalization.C450Source34GroupedC09.valid3
#print axioms N11Formalization.C450Source34GroupedC09.valid4
#print axioms N11Formalization.C450Source34GroupedC09.valid5
#print axioms N11Formalization.C450Source34GroupedC09.valid6
#print axioms N11Formalization.C450Source34GroupedC09.valid7
#print axioms N11Formalization.C450Source34GroupedC09.valid8
#print axioms N11Formalization.C450Source34GroupedC09.valid9
#print axioms N11Formalization.C450Source34GroupedC09.valid10
#print axioms N11Formalization.C450Source34GroupedC09.valid11
#print axioms N11Formalization.C450Source34GroupedC09.valid12
#print axioms N11Formalization.C450Source34GroupedC09.bound
#print axioms N11Formalization.C450Source34GroupedC09.endpoint_checks
