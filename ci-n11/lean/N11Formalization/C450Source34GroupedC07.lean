import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((6829009737:ℚ)/10000000000),((705916607:ℚ)/1000000000),((-501116607:ℚ)/992000000),((-13447029211:ℚ)/33700000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1135832711:ℚ)/2500000000),((79932412831322037872957271029669:ℚ)/246016000000000000000000000000000),((406910390959954117917679891:ℚ)/1108992000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1737373621:ℚ)/2500000000),((13904959:ℚ)/19531250),((-13206612:ℚ)/26328125),((-10356362589:ℚ)/25512500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4167553567:ℚ)/10000000000),((1425767773099406643415392232583:ℚ)/4436289062500000000000000000000),((8348914656604806739606233:ℚ)/23104000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((1401942423:ℚ)/2000000000),((3589748467:ℚ)/5000000000),((-2565748467:ℚ)/5102500000),((-8393481807:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((495909019:ℚ)/1250000000),((965145859621508761224187631870579:ℚ)/3004096875000000000000000000000000),((15905418521955114298840531:ℚ)/44359680000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((56559311:ℚ)/80000000),((723964027:ℚ)/1000000000),((-519164027:ℚ)/1030000000),((-113357933:ℚ)/277200000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((3756977587:ℚ)/10000000000),((42592706000531402702151453229387:ℚ)/132612500000000000000000000000000),((8416047271862031838273:ℚ)/23658496000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1782525053:ℚ)/2500000000),((456235589:ℚ)/625000000),((-3315511:ℚ)/6562500),((-10762725477:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3534876909:ℚ)/10000000000),((7024112847300559575891909077:ℚ)/21875000000000000000000000000),((8153086573343936409456617:ℚ)/23104000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((3595135779:ℚ)/5000000000),((7359884787:ℚ)/10000000000),((-5311884787:ℚ)/10490000000),((-21796222011:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1649289773:ℚ)/5000000000),((8831758613542696405987540206790543:ℚ)/27510025000000000000000000000000000),((97043318937140422733781499:ℚ)/277248000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((290017133:ℚ)/400000000),((1483997347:ℚ)/2000000000),((-1074397347:ℚ)/2117000000),((-588451399:ℚ)/1424000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((608954991:ℚ)/2000000000),((539462662119911195882106346043801:ℚ)/1680633375000000000000000000000000),((205321371060276223018057:ℚ)/591462400000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3655285457:ℚ)/5000000000),((754015183:ℚ)/1000000000),((-549215183:ℚ)/1068000000),((-22337569113:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((692161253:ℚ)/2500000000),((30792360157807610265498939739111:ℚ)/95052000000000000000000000000000),((31813419555757504152011137:ℚ)/92416000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7430815079:ℚ)/10000000000),((7660267463:ℚ)/10000000000),((-5612267463:ℚ)/10870000000),((-45757335711:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2113965989:ℚ)/10000000000),((3587511847191395636001636422604443:ℚ)/11077209375000000000000000000000000),((125088482564816658079166033:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7551006969:ℚ)/10000000000),((7900360417:ℚ)/10000000000),((-5852360417:ℚ)/11060000000),((-4258096611:ℚ)/10400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1136080061:ℚ)/10000000000),((10079830854382964672329832392695647:ℚ)/30580900000000000000000000000000000),((368686472953847528201360179:ℚ)/1108992000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((973905573:ℚ)/1250000000),((8859191001:ℚ)/10000000000),((-6811191001:ℚ)/11440000000),((-2041716719:ℚ)/5400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((35631935582921747050739244187671271:ℚ)/98155200000000000000000000000000000),((42241459:ℚ)/128000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((8750566603:ℚ)/10000000000),((10771769579:ℚ)/10000000000),((-107700859:ℚ)/160000000),((-57635099427:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((7673245086954888334701413952709:ℚ)/19200000000000000000000000000000),((42241459:ℚ)/128000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((10663842313:ℚ)/10000000000),((7293238061:ℚ)/5000000000),((-6269238061:ℚ)/8000000000),((-24951526939:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((761083870512372196017843:ℚ)/1600000000000000000000000),((42241459:ℚ)/128000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((553:ℚ)/800) :=
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
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC07
#check @N11Formalization.C450Source34GroupedC07.bound
#print axioms N11Formalization.C450Source34GroupedC07.valid0
#print axioms N11Formalization.C450Source34GroupedC07.valid1
#print axioms N11Formalization.C450Source34GroupedC07.valid2
#print axioms N11Formalization.C450Source34GroupedC07.valid3
#print axioms N11Formalization.C450Source34GroupedC07.valid4
#print axioms N11Formalization.C450Source34GroupedC07.valid5
#print axioms N11Formalization.C450Source34GroupedC07.valid6
#print axioms N11Formalization.C450Source34GroupedC07.valid7
#print axioms N11Formalization.C450Source34GroupedC07.valid8
#print axioms N11Formalization.C450Source34GroupedC07.valid9
#print axioms N11Formalization.C450Source34GroupedC07.valid10
#print axioms N11Formalization.C450Source34GroupedC07.valid11
#print axioms N11Formalization.C450Source34GroupedC07.valid12
#print axioms N11Formalization.C450Source34GroupedC07.bound
#print axioms N11Formalization.C450Source34GroupedC07.endpoint_checks
