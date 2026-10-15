import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((6207008997:ℚ)/10000000000),((6724729117:ℚ)/10000000000),((-1924729117:ℚ)/49600000000),((4032991003:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((153776749:ℚ)/250000000),((7425620490040487588318726681541816767:ℚ)/122023936000000000000000000000000000000),((-3291427274464078258557268193:ℚ)/44359680000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6684367913:ℚ)/10000000000),((3422005289:ℚ)/5000000000),((-1022005289:ℚ)/26700000000),((3555632087:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4959393647:ℚ)/10000000000),((671772246956368385309231717211143212336756359398853633907:ℚ)/11420497800000000000000000000000000000000000000000000000000),((-1251750895012648099823654771:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((106307121:ℚ)/156250000),((348163683:ℚ)/500000000),((-108163683:ℚ)/2717500000),((53692879:ℚ)/1698437500),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2309382397:ℚ)/5000000000),((168069033910943639563162717635899735384104124355359:ℚ)/2870780608803033828735351562500000000000000000000000),((-945129143127275543514857:ℚ)/10830000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((276916999:ℚ)/400000000),((885314913:ℚ)/1250000000),((-285314913:ℚ)/6912500000),((132683001:ℚ)/4424000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4253092461:ℚ)/10000000000),((2253244136849186366080277576846988985649157237738641:ℚ)/38654257600000000000000000000000000000000000000000000),((-2126540422057500908683859:ℚ)/23658496000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((1760544139:ℚ)/2500000000),((7142135861:ℚ)/10000000000),((-2342135861:ℚ)/56250000000),((88828429:ℚ)/3125000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3855222293:ℚ)/10000000000),((5528280827561997282917990406299636703635679415459803:ℚ)/95367431640625000000000000000000000000000000000000000),((-85485344916049528943453739:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((887724501:ℚ)/1250000000),((7201748383:ℚ)/10000000000),((-2401748383:ℚ)/56725000000),((392275499:ℚ)/14181250000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((728187611:ℚ)/2000000000),((20627655342029558168016754081420443426873235184561213:ℚ)/356495089996337890625000000000000000000000000000000000),((-65020633747684430910592577:ℚ)/693120000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((3580705687:ℚ)/5000000000),((726135697:ℚ)/1000000000),((-246135697:ℚ)/5720000000),((1539294313:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3413877231:ℚ)/10000000000),((25336085785857537828659506673666224424304539248332221213:ℚ)/438631050000000000000000000000000000000000000000000000000),((-351612467626555351206192371:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((3610511379:ℚ)/5000000000),((3660480859:ℚ)/5000000000),((-1260480859:ℚ)/28837500000),((1509488621:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3171291667:ℚ)/10000000000),((460969377291133376686639885506373036065233286935211121:ℚ)/7993768517578125000000000000000000000000000000000000000),((-1069345952592923820856335857:ℚ)/11089920000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((3640315129:ℚ)/5000000000),((930020009:ℚ)/1250000000),((-330020009:ℚ)/7268750000),((1479684871:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((727323781:ℚ)/2500000000),((26575750685506450305949469947409949320045252503288095011:ℚ)/460850902441406250000000000000000000000000000000000000000),((-361285270836008915238273619:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((369991699:ℚ)/500000000),((383925733:ℚ)/500000000),((-143925733:ℚ)/2955000000),((142008301:ℚ)/5910000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2300176733:ℚ)/10000000000),((111619503975971643237125360897115759371092526918123489:ℚ)/1935235040625000000000000000000000000000000000000000000),((-3709598507519870285259259:ℚ)/36966400000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((7638198797:ℚ)/10000000000),((4077536379:ℚ)/5000000000),((-1677536379:ℚ)/30500000000),((2601801203:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((81904079249563929173571694555057515513983615169069321101:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-107260969:ℚ)/1024000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((507173471:ℚ)/625000000),((251495491:ℚ)/250000000),((-131495491:ℚ)/1620000000),((132826529:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((18459747648552528787492425590252185805479622170263229:ℚ)/311391210937500000000000000000000000000000000000000000),((-107260969:ℚ)/1024000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((10019554207:ℚ)/10000000000),((6932691783:ℚ)/5000000000),((-4532691783:ℚ)/40000000000),((220445793:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((33308922942249973961163651441609464597:ℚ)/512000000000000000000000000000000000000),((-107260969:ℚ)/1024000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC15
#check @N11Formalization.C450Source17GroupedC15.bound
#print axioms N11Formalization.C450Source17GroupedC15.valid0
#print axioms N11Formalization.C450Source17GroupedC15.valid1
#print axioms N11Formalization.C450Source17GroupedC15.valid2
#print axioms N11Formalization.C450Source17GroupedC15.valid3
#print axioms N11Formalization.C450Source17GroupedC15.valid4
#print axioms N11Formalization.C450Source17GroupedC15.valid5
#print axioms N11Formalization.C450Source17GroupedC15.valid6
#print axioms N11Formalization.C450Source17GroupedC15.valid7
#print axioms N11Formalization.C450Source17GroupedC15.valid8
#print axioms N11Formalization.C450Source17GroupedC15.valid9
#print axioms N11Formalization.C450Source17GroupedC15.valid10
#print axioms N11Formalization.C450Source17GroupedC15.valid11
#print axioms N11Formalization.C450Source17GroupedC15.valid12
#print axioms N11Formalization.C450Source17GroupedC15.bound
#print axioms N11Formalization.C450Source17GroupedC15.endpoint_checks
