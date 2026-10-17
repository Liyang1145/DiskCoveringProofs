import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6607654777:ℚ)/10000000000),((426148833:ℚ)/625000000),((-286148833:ℚ)/775000000),((-27693583439:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5167524169:ℚ)/10000000000),((294521006877148449402057842693118307:ℚ)/1278982136718750000000000000000000000),((458215736328840740377165373:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((134559451:ℚ)/200000000),((3469316211:ℚ)/5000000000),((-2349316211:ℚ)/6318750000),((-570716157:ℚ)/2060000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4837445653:ℚ)/10000000000),((26773705107847886824860499035315026015038168326815593159:ℚ)/116167727444744110107421875000000000000000000000000000000),((175185878322432764794437:ℚ)/1182924800000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((54785851:ℚ)/80000000),((699873701:ℚ)/1000000000),((-475873701:ℚ)/1287500000),((-78340319:ℚ)/277200000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((560669571:ℚ)/1250000000),((1904292275504196088362132152207843944717223331546258973:ℚ)/8341170136499404907226562500000000000000000000000000000),((26720044043345470108037:ℚ)/189267968000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((3454169859:ℚ)/5000000000),((3529414071:ℚ)/5000000000),((-2409414071:ℚ)/6496875000),((-14899189013:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((34394949:ℚ)/80000000),((23026038485252813679303037265704067444564291813541404999:ℚ)/100796981782722473144531250000000000000000000000000000000),((305391559420459902927218591:ℚ)/2217984000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((1393686907:ℚ)/2000000000),((7118906191:ℚ)/10000000000),((-4878906191:ℚ)/13112500000),((-6043808349:ℚ)/21170000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1026388581:ℚ)/2500000000),((197741855009685312029240539399264885962110446673289348687613:ℚ)/865078217822961425781250000000000000000000000000000000000000),((15872938933929538785713413:ℚ)/118292480000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((7028516201:ℚ)/10000000000),((7178971513:ℚ)/10000000000),((-4938971513:ℚ)/13231250000),((-10213204469:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1951371187:ℚ)/5000000000),((26229120056584079126598993286404136819170333774198170861017:ℚ)/114673391404072570800781250000000000000000000000000000000000),((386404842911618700091681437:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((7088585073:ℚ)/10000000000),((3619512227:ℚ)/5000000000),((-2499512227:ℚ)/6675000000),((-31060095511:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((368944359:ℚ)/1000000000),((8781140411453194806511219950468169745002768571824279512833:ℚ)/38365941330761718750000000000000000000000000000000000000000),((1127798486115383854937187719:ℚ)/8871936000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7148641499:ℚ)/10000000000),((14255987:ℚ)/19531250),((-316191584:ℚ)/841796875),((-31480490493:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((173185761:ℚ)/500000000),((516566304199996299404069105771203700631448444369531482641927:ℚ)/2255438523599600791931152343750000000000000000000000000000000),((365407405101914322736941637:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7208685811:ℚ)/10000000000),((919886813:ℚ)/1250000000),((-639886813:ℚ)/1698437500),((-31900800677:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3222940459:ℚ)/10000000000),((1875100098909123398538863563990067124820273310218821801091:ℚ)/8181510383469855785369873046875000000000000000000000000000),((354828548006086978773160277:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7268718333:ℚ)/10000000000),((1854778061:ℚ)/2500000000),((-431592687:ℚ)/1142187500),((-32321028331:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((370430929:ℚ)/1250000000),((28593524293712629939003531396054469588714050335535926531:ℚ)/124673769416046142578125000000000000000000000000000000000),((1032588700520397303960830879:ℚ)/8871936000000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((7328739373:ℚ)/10000000000),((3769557321:ℚ)/5000000000),((-2649557321:ℚ)/6912500000),((-32741175611:ℚ)/112500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((334974599:ℚ)/1250000000),((1844979044975078993941725602323387792358305977889700431:ℚ)/7962531701660156250000000000000000000000000000000000000),((333510439343823751188001173:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((7448748201:ℚ)/10000000000),((7659074801:ℚ)/10000000000),((-1806358267:ℚ)/4687500000),((-33581237407:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1998395211:ℚ)/10000000000),((84831890914091817255494627350806881454149715748245405227:ℚ)/365656614303588867187500000000000000000000000000000000000),((2592617651898091148405951:ℚ)/24576000000000000000000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((756871457:ℚ)/1000000000),((8617462289:ℚ)/10000000000),((-579769299:ℚ)/1300000000),((-1147366733:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((907670793:ℚ)/10000000000),((72569743175083121195114281327315358504614381562964601:ℚ)/278057812500000000000000000000000000000000000000000000),((2902320359716409888652813:ℚ)/29573120000000000000000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8527145013:ℚ)/10000000000),((2105882409:ℚ)/2000000000),((-1657882409:ℚ)/3240000000),((-41130015091:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((744725236291685913899666458546017464771:ℚ)/2592000000000000000000000000000000000000),((19703911:ℚ)/204800000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((10439155741:ℚ)/10000000000),((7171693107:ℚ)/5000000000),((-6051693107:ℚ)/10000000000),((-54514090187:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2744586174486911638159544843:ℚ)/8125440000000000000000000000),((19703911:ℚ)/204800000)⟩
theorem valid14 : Valid source30 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source30 nn0 nn1 Qcell ((2079:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source30 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((45:ℚ)/64) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC09
#check @N11Formalization.C450Source30GroupedC09.bound
#print axioms N11Formalization.C450Source30GroupedC09.valid0
#print axioms N11Formalization.C450Source30GroupedC09.valid1
#print axioms N11Formalization.C450Source30GroupedC09.valid2
#print axioms N11Formalization.C450Source30GroupedC09.valid3
#print axioms N11Formalization.C450Source30GroupedC09.valid4
#print axioms N11Formalization.C450Source30GroupedC09.valid5
#print axioms N11Formalization.C450Source30GroupedC09.valid6
#print axioms N11Formalization.C450Source30GroupedC09.valid7
#print axioms N11Formalization.C450Source30GroupedC09.valid8
#print axioms N11Formalization.C450Source30GroupedC09.valid9
#print axioms N11Formalization.C450Source30GroupedC09.valid10
#print axioms N11Formalization.C450Source30GroupedC09.valid11
#print axioms N11Formalization.C450Source30GroupedC09.valid12
#print axioms N11Formalization.C450Source30GroupedC09.valid13
#print axioms N11Formalization.C450Source30GroupedC09.valid14
#print axioms N11Formalization.C450Source30GroupedC09.bound
#print axioms N11Formalization.C450Source30GroupedC09.endpoint_checks
