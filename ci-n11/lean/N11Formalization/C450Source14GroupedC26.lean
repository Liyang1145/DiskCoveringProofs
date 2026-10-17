import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((293084871:ℚ)/500000000),((1278638361:ℚ)/2000000000),((1007254613:ℚ)/1780000000),((1445038361:ℚ)/1984000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6899529297:ℚ)/10000000000),((-15592246983009580048362754308409:ℚ)/1409938000000000000000000000000000),((-138627828035135532647962731:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((1584411467:ℚ)/2500000000),((3315549097:ℚ)/5000000000),((16179703203:ℚ)/27650000000),((1243849699:ℚ)/1780000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2923291063:ℚ)/5000000000),((-2033969489485224220098645474687150552908095323704075397:ℚ)/132119044531250000000000000000000000000000000000000000000),((-871839850406375682944452299:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6575571079:ℚ)/10000000000),((85862219:ℚ)/125000000),((66860139711:ℚ)/114400000000),((96262219:ℚ)/138250000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5252338271:ℚ)/10000000000),((-147089710957641964072867417898116226568593786534349121929:ℚ)/9357462400000000000000000000000000000000000000000000000000),((-546537281208305654664771:ℚ)/2310400000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((681346797:ℚ)/1000000000),((6987907867:ℚ)/10000000000),((6900121173:ℚ)/11630000000),((7819907867:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1147426949:ℚ)/2500000000),((-43164977118247057254974184143084778079916793986748867:ℚ)/2457871479687500000000000000000000000000000000000000000),((-3508646014241242391258945379:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((9:ℚ)/16),((5:ℚ)/8),((6932406667:ℚ)/10000000000),((7047370843:ℚ)/10000000000),((70071660003:ℚ)/117250000000),((7879370843:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1055688423:ℚ)/2500000000),((-99052372957438427291200042031725176370921009565824977:ℚ)/5370141601562500000000000000000000000000000000000000000),((-3514047034807411536171027939:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((1747968429:ℚ)/2500000000),((3553416201:ℚ)/5000000000),((5883905287:ℚ)/9850000000),((3969416201:ℚ)/5862500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4027582371:ℚ)/10000000000),((-27585369260236869596770241743665099725091332482944657:ℚ)/1493236914062500000000000000000000000000000000000000000),((-879164497699160274999865611:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((7051339283:ℚ)/10000000000),((3583146289:ℚ)/5000000000),((71142053547:ℚ)/119150000000),((1333048763:ℚ)/1970000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1911516923:ℚ)/5000000000),((-195580511891847444858679862192412714686918958122500147893:ℚ)/10572121786718750000000000000000000000000000000000000000000),((-879816847727671599922559931:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((3555401701:ℚ)/5000000000),((7225751403:ℚ)/10000000000),((35838615309:ℚ)/60050000000),((8057751403:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3607509301:ℚ)/10000000000),((-1566822733220243997688117510892101073166776221845900819:ℚ)/84586113330078125000000000000000000000000000000000000000),((-3521875236750304780380535299:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((1792566527:ℚ)/2500000000),((728520891:ℚ)/1000000000),((6017699581:ℚ)/10087500000),((811720891:ℚ)/1201000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((844726187:ℚ)/2500000000),((-4406468381131716492897725434529631517192307008985593:ℚ)/237611193847656250000000000000000000000000000000000000),((-35244815299568606451657891:ℚ)/147865600000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((3614863717:ℚ)/5000000000),((734466513:ℚ)/1000000000),((36373773453:ℚ)/61000000000),((817666513:ℚ)/1210500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((78358873:ℚ)/250000000),((-26335606752412189502373501749434254365867089784239424067:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-35270862720808217461345659:ℚ)/147865600000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((7289187413:ℚ)/10000000000),((298542953:ℚ)/400000000),((24427562239:ℚ)/41300000000),((331822953:ℚ)/488000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((286978139:ℚ)/1000000000),((-1962162448662925002930084250098859523416146801987345729:ℚ)/110070307812500000000000000000000000000000000000000000000),((-297221317041453955161321:ℚ)/1245184000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3704051727:ℚ)/5000000000),((7582477717:ℚ)/10000000000),((1004769339:ℚ)/1700000000),((8414477717:ℚ)/12390000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2251955749:ℚ)/10000000000),((-535811771179950391610543976043656931725437217741:ℚ)/29986572265625000000000000000000000000000000000000),((-3534701909571168106652491779:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((1881753617:ℚ)/2500000000),((7820271939:ℚ)/10000000000),((6285260851:ℚ)/10800000000),((8652271939:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((693497287:ℚ)/5000000000),((-4810372075898906249549956279845853797935766820272647:ℚ)/291600000000000000000000000000000000000000000000000000),((-3639207931454967:ℚ)/15200000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7764822307:ℚ)/10000000000),((9722121899:ℚ)/10000000000),((77563400763:ℚ)/160000000000),((1172680211:ℚ)/1440000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-14360091036954635439954992179100509:ℚ)/6000000000000000000000000000000000000),((-245404689:ℚ)/1024000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((9666757851:ℚ)/10000000000),((135242923:ℚ)/100000000),((31560273553:ℚ)/73600000000),((143562923:ℚ)/160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1486434477816316888589827:ℚ)/169280000000000000000000000),((-245404689:ℚ)/1024000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC26
#check @N11Formalization.C450Source14GroupedC26.bound
#print axioms N11Formalization.C450Source14GroupedC26.valid0
#print axioms N11Formalization.C450Source14GroupedC26.valid1
#print axioms N11Formalization.C450Source14GroupedC26.valid2
#print axioms N11Formalization.C450Source14GroupedC26.valid3
#print axioms N11Formalization.C450Source14GroupedC26.valid4
#print axioms N11Formalization.C450Source14GroupedC26.valid5
#print axioms N11Formalization.C450Source14GroupedC26.valid6
#print axioms N11Formalization.C450Source14GroupedC26.valid7
#print axioms N11Formalization.C450Source14GroupedC26.valid8
#print axioms N11Formalization.C450Source14GroupedC26.valid9
#print axioms N11Formalization.C450Source14GroupedC26.valid10
#print axioms N11Formalization.C450Source14GroupedC26.valid11
#print axioms N11Formalization.C450Source14GroupedC26.valid12
#print axioms N11Formalization.C450Source14GroupedC26.valid13
#print axioms N11Formalization.C450Source14GroupedC26.valid14
#print axioms N11Formalization.C450Source14GroupedC26.bound
#print axioms N11Formalization.C450Source14GroupedC26.endpoint_checks
