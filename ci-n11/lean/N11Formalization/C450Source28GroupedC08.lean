import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((831778977:ℚ)/1250000000),((1715709587:ℚ)/2500000000),((-11281386283:ℚ)/24800000000),((-187259659:ℚ)/526562500),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2521045771:ℚ)/5000000000),((21922817284856784792250089732307593937201028692412857:ℚ)/84861899113655090332031250000000000000000000000000000),((48798224184147689065528881:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6774230691:ℚ)/10000000000),((1396553921:ℚ)/2000000000),((-9240985289:ℚ)/20220000000),((-4614230691:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4704902723:ℚ)/10000000000),((3487114075106425669854092261728034857524023718969991249259:ℚ)/13485681115722656250000000000000000000000000000000000000000),((3044239785982078608144510009:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((1723545697:ℚ)/2500000000),((7042718803:ℚ)/10000000000),((-46744469227:ℚ)/103000000000),((-1183545697:ℚ)/3248437500),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1085960861:ℚ)/2500000000),((4226597230014573451225585708156172898316412455977296923:ℚ)/16550154465740919113159179687500000000000000000000000000),((185289956040040433860410801:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6954142113:ℚ)/10000000000),((7102657453:ℚ)/10000000000),((-47283917077:ℚ)/103950000000),((-4794142113:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1038105141:ℚ)/2500000000),((170136470400161540185264479232151354111296127846136219943:ℚ)/665791634097290039062500000000000000000000000000000000000),((2924556067630123409217800241:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-9:ℚ)/16),((-1:ℚ)/2),((7014090701:ℚ)/10000000000),((3566311457:ℚ)/5000000000),((-23776803113:ℚ)/52450000000),((-4854090701:ℚ)/13171875000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((19761677:ℚ)/50000000),((1409545966973022928985019310093747571989360208168014213:ℚ)/5549253227472305297851562500000000000000000000000000000),((2884284050747528226665972889:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7044061061:ℚ)/10000000000),((1790646461:ℚ)/2500000000),((-11955818149:ℚ)/26343750000),((-4884061061:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((384862297:ℚ)/1000000000),((3101020662636846802510519595173512201971281685811933379237:ℚ)/12204225344480895996093750000000000000000000000000000000000),((2864077217399269250026911369:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((3537014423:ℚ)/5000000000),((179813657:ℚ)/250000000),((-1202322913:ℚ)/2646250000),((-2457014423:ℚ)/6645312500),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3742193497:ℚ)/10000000000),((986938663229125286494935329617672732344883337189220583741:ℚ)/3882818601618027687072753906250000000000000000000000000000),((710955788083601531906228481:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((7103994091:ℚ)/10000000000),((3611252127:ℚ)/5000000000),((-24181269143:ℚ)/53162500000),((-4943994091:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((908201881:ℚ)/2500000000),((4020219496033143459670035978055514102058753499211186695517:ℚ)/15810995163867187500000000000000000000000000000000000000000),((2823521844434251609030183209:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((7133956831:ℚ)/10000000000),((7252459801:ℚ)/10000000000),((-48632138209:ℚ)/106800000000),((-4973956831:ℚ)/13409375000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((1760094387:ℚ)/5000000000),((15990934804209272666229302664162754722548485769584776983:ℚ)/62869052242210507392883300781250000000000000000000000000),((2803173282350320315043598129:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((7163917101:ℚ)/10000000000),((7282412953:ℚ)/10000000000),((-6985959511:ℚ)/15325000000),((-5003917101:ℚ)/13468750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((34040157:ℚ)/100000000),((9303890810156875906444311548578043524645270576282874467:ℚ)/36566416534036397933959960937500000000000000000000000000),((2782777454504376875062912089:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1798468733:ℚ)/2500000000),((3671156099:ℚ)/5000000000),((-24720404891:ℚ)/53875000000),((-1258468733:ℚ)/3396875000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1641955201:ℚ)/5000000000),((27045794028178845228262054524009127199405546663508377873:ℚ)/105583483084297180175781250000000000000000000000000000000),((172645896988833376393990521:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7253783411:ℚ)/10000000000),((7402202241:ℚ)/10000000000),((-49979820169:ℚ)/108700000000),((-5093783411:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1515007461:ℚ)/5000000000),((373628520982020630931449362684847969292401053882049011621:ℚ)/1457754069386672973632812500000000000000000000000000000000),((2721306277761234458215430169:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((1828420631:ℚ)/2500000000),((7462083323:ℚ)/10000000000),((-69109097:ℚ)/150000000),((-1288420631:ℚ)/3456250000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2753626869:ℚ)/10000000000),((1033997727703295796114625413974840016123568753394861:ℚ)/4031953263282775878906250000000000000000000000000000),((167505561117728313855446529:ℚ)/924160000000000000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((1474714503:ℚ)/2000000000),((3790909763:ℚ)/5000000000),((-25798187867:ℚ)/55300000000),((-115857167:ℚ)/312500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2447129541:ℚ)/10000000000),((321043362745073531463170641687758465800482185741143:ℚ)/1236051321029663085937500000000000000000000000000000),((105547294994377826117837601:ℚ)/591462400000000000000000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((3746663037:ℚ)/5000000000),((3850761287:ℚ)/5000000000),((-26336851583:ℚ)/56250000000),((-2666663037:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((419359653:ℚ)/2500000000),((5344760077657255285524353410018570927413691811870866943:ℚ)/20560830468750000000000000000000000000000000000000000000),((638825239284028728410635641:ℚ)/3696640000000000000000000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((59476921:ℚ)/78125000),((8658130801:ℚ)/10000000000),((-61283177209:ℚ)/114400000000),((-42601921:ℚ)/126562500),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((16472141689489111087054793686376652579400262722849:ℚ)/54905676841735839843750000000000000000000000000000),((171770643:ℚ)/1024000000)⟩
theorem valid15 : Valid source28 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((8569770181:ℚ)/10000000000),((10567553027:ℚ)/10000000000),((-78467977243:ℚ)/129600000000),((-6409770181:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1347352037291826588948501479537895604416150119927860824479:ℚ)/4050000000000000000000000000000000000000000000000000000000),((171770643:ℚ)/1024000000)⟩
theorem valid16 : Valid source28 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((5239678703:ℚ)/5000000000),((7189290217:ℚ)/5000000000),((-56383611953:ℚ)/80000000000),((-4159678703:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((165193909700358481945376516952039256197002432443467062136227:ℚ)/423200000000000000000000000000000000000000000000000000000000),((171770643:ℚ)/1024000000)⟩
theorem valid17 : Valid source28 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source28 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source28 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source28 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC08
#check @N11Formalization.C450Source28GroupedC08.bound
#print axioms N11Formalization.C450Source28GroupedC08.valid0
#print axioms N11Formalization.C450Source28GroupedC08.valid1
#print axioms N11Formalization.C450Source28GroupedC08.valid2
#print axioms N11Formalization.C450Source28GroupedC08.valid3
#print axioms N11Formalization.C450Source28GroupedC08.valid4
#print axioms N11Formalization.C450Source28GroupedC08.valid5
#print axioms N11Formalization.C450Source28GroupedC08.valid6
#print axioms N11Formalization.C450Source28GroupedC08.valid7
#print axioms N11Formalization.C450Source28GroupedC08.valid8
#print axioms N11Formalization.C450Source28GroupedC08.valid9
#print axioms N11Formalization.C450Source28GroupedC08.valid10
#print axioms N11Formalization.C450Source28GroupedC08.valid11
#print axioms N11Formalization.C450Source28GroupedC08.valid12
#print axioms N11Formalization.C450Source28GroupedC08.valid13
#print axioms N11Formalization.C450Source28GroupedC08.valid14
#print axioms N11Formalization.C450Source28GroupedC08.valid15
#print axioms N11Formalization.C450Source28GroupedC08.valid16
#print axioms N11Formalization.C450Source28GroupedC08.valid17
#print axioms N11Formalization.C450Source28GroupedC08.bound
#print axioms N11Formalization.C450Source28GroupedC08.endpoint_checks
