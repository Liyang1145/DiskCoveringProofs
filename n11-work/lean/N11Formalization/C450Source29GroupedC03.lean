import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((22017031:ℚ)/31250000),((7215846007:ℚ)/10000000000),((-41870922049:ℚ)/49600000000),((-230221403:ℚ)/312968750),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((3843752453:ℚ)/10000000000),((226338038238941351290991770413772483:ℚ)/608197448332519531250000000000000000),((1517773047329554961927708263:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7105130497:ℚ)/10000000000),((7275442923:ℚ)/10000000000),((-42288100461:ℚ)/50075000000),((-24815565487:ℚ)/33700000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((145143889:ℚ)/400000000),((6960934232798122313810680359712633349629431153165691121:ℚ)/18715899477294921875000000000000000000000000000000000000),((4562022225410991269427793469:ℚ)/5544960000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((895600661:ℚ)/1250000000),((1833758921:ℚ)/2500000000),((-10676312447:ℚ)/12637500000),((-9402808593:ℚ)/12756250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((3400513557:ℚ)/10000000000),((1940847498311837908866351448940777461150913698784607739:ℚ)/5221323526668548583984375000000000000000000000000000000),((95223545569089996941012967:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((1444894891:ℚ)/2000000000),((7394624407:ℚ)/10000000000),((-43122370849:ℚ)/51025000000),((-15199633583:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((3156694991:ℚ)/10000000000),((4971419232918453792765310793972866878477843968363799498521:ℚ)/13381534842000000000000000000000000000000000000000000000000),((1526481014556687065566519463:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1821034539:ℚ)/2500000000),((7454209203:ℚ)/10000000000),((-43539464421:ℚ)/51500000000),((-19193449007:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2893160409:ℚ)/10000000000),((16387705309285610487961524937976355559078796470151983709:ℚ)/44133745241975784301757812500000000000000000000000000000),((4588160809602648310963997549:ℚ)/5544960000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7343796543:ℚ)/10000000000),((3756895089:ℚ)/5000000000),((-7326088541:ℚ)/8662500000),((-77549355059:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((520784851:ℚ)/2000000000),((1855533660826941931719569161375619814412869117813116744469923:ℚ)/4999651310981250000000000000000000000000000000000000000000000),((1149220874888303836389989381:ℚ)/1386240000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((7403449761:ℚ)/10000000000),((7632941081:ℚ)/10000000000),((-44790587567:ℚ)/52450000000),((-78324846893:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((569803931:ℚ)/2500000000),((1001285065619382394044561880444059960876898623065958064346291:ℚ)/2662244931600000000000000000000000000000000000000000000000000),((106406149:ℚ)/128000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((3761370623:ℚ)/5000000000),((4054705459:ℚ)/5000000000),((-24062938213:ℚ)/26700000000),((-39937818099:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),((285417529:ℚ)/2000000000),((126410141114721746850144622323979438480055052573698467188557:ℚ)/312305307600000000000000000000000000000000000000000000000000),((106406149:ℚ)/128000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((1999931553:ℚ)/2500000000),((4530915739:ℚ)/5000000000),((-2490582743:ℚ)/2600000000),((-21519110189:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((902327179996369404585890741201585205199279998989384755199:ℚ)/2072619900000000000000000000000000000000000000000000000000),((106406149:ℚ)/128000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((8952994177:ℚ)/10000000000),((5482644591:ℚ)/5000000000),(-1:ℚ),((-98468924301:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((737478911056962170151861878806330158306282087574731244801:ℚ)/1600000000000000000000000000000000000000000000000000000000),((106406149:ℚ)/128000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((1085766063:ℚ)/1000000000),((7384671857:ℚ)/5000000000),(-1:ℚ),((-12322958819:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1281621582753625194617055989451900997:ℚ)/2691145728000000000000000000000000000),((106406149:ℚ)/128000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC03
#check @N11Formalization.C450Source29GroupedC03.bound
#print axioms N11Formalization.C450Source29GroupedC03.valid0
#print axioms N11Formalization.C450Source29GroupedC03.valid1
#print axioms N11Formalization.C450Source29GroupedC03.valid2
#print axioms N11Formalization.C450Source29GroupedC03.valid3
#print axioms N11Formalization.C450Source29GroupedC03.valid4
#print axioms N11Formalization.C450Source29GroupedC03.valid5
#print axioms N11Formalization.C450Source29GroupedC03.valid6
#print axioms N11Formalization.C450Source29GroupedC03.valid7
#print axioms N11Formalization.C450Source29GroupedC03.valid8
#print axioms N11Formalization.C450Source29GroupedC03.valid9
#print axioms N11Formalization.C450Source29GroupedC03.valid10
#print axioms N11Formalization.C450Source29GroupedC03.bound
#print axioms N11Formalization.C450Source29GroupedC03.endpoint_checks
