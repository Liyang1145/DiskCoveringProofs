import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((1261839107:ℚ)/2000000000),((6618254971:ℚ)/10000000000),((-2618254971:ℚ)/24800000000),((-457517321:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5914065513:ℚ)/10000000000),((299317198901017870922643878203001002906223010260113570937:ℚ)/1693726850000000000000000000000000000000000000000000000000),((-83886394246478384433671373:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((3274809669:ℚ)/5000000000),((3369228847:ℚ)/5000000000),((-1369228847:ℚ)/12875000000),((-1504429007:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((532004457:ℚ)/1000000000),((4037580599650215309665575851896431415072571229101497508767:ℚ)/23221684931054687500000000000000000000000000000000000000000),((-574915778999755786990570397:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((3334875201:ℚ)/5000000000),((685860781:ℚ)/1000000000),((-285860781:ℚ)/2622500000),((-1684625603:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((999932521:ℚ)/2000000000),((14440354115010383215060960491608731979181645951361939536847:ℚ)/83195154112500000000000000000000000000000000000000000000000),((-600337732532975763655383077:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6789831499:ℚ)/10000000000),((3489354071:ℚ)/5000000000),((-496451357:ℚ)/4450000000),((-3729494497:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((145606787:ℚ)/312500000),((123825369232471386633369266644117979245104790162160277119199:ℚ)/714428311043750000000000000000000000000000000000000000000000),((-2503332269281074162952241277:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((863733163:ℚ)/1250000000),((3519370233:ℚ)/5000000000),((-1519370233:ℚ)/13587500000),((-511199489:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4294550149:ℚ)/10000000000),((27879657756579060498158704387194536288861900367589363803:ℚ)/161972674376296997070312500000000000000000000000000000000),((-40712640583326632230023613:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((6969865257:ℚ)/10000000000),((221836291:ℚ)/312500000),((-96836291:ℚ)/856640625),((-609942253:ℚ)/15800000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4100835051:ℚ)/10000000000),((48442689172539718221818732393155113201850184912399545001:ℚ)/281571491406250000000000000000000000000000000000000000000),((-2656858679339880420344723573:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7029854307:ℚ)/10000000000),((3609384881:ℚ)/5000000000),((-1609384881:ℚ)/13825000000),((-4449562921:ℚ)/112500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((194905591:ℚ)/500000000),((1108190245355202092507708397896363849691302181669998700197:ℚ)/6407690048217773437500000000000000000000000000000000000000),((-2708182849834221957865576973:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((285992033:ℚ)/400000000),((1467747153:ℚ)/2000000000),((-667747153:ℚ)/5625000000),((-192376099:ℚ)/4576000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((864804771:ℚ)/2500000000),((310489083720641894728256864659223821342131897636355999:ℚ)/1796632780800000000000000000000000000000000000000000000),((-4497688706702165696183653:ℚ)/23658496000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((908713377:ℚ)/1250000000),((7578548783:ℚ)/10000000000),((-3578548783:ℚ)/28600000000),((-646140131:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((591797889:ℚ)/2000000000),((13981606284734154896049298512272816399895894584348155739:ℚ)/80074829516601562500000000000000000000000000000000000000),((-45534816824736077381941733:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((7509406341:ℚ)/10000000000),((7818215731:ℚ)/10000000000),((-1272738577:ℚ)/9850000000),((-5888219023:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1545572763:ℚ)/10000000000),((390040319234885767816367750503726256223522130781243005209453:ℚ)/2235762850000000000000000000000000000000000000000000000000000),((-3121480199170029333936695837:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((7748966869:ℚ)/10000000000),((8297163681:ℚ)/10000000000),((-4297163681:ℚ)/30500000000),((-6606900607:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5469099104746835675410879868599095680861933998924136839823:ℚ)/30736972800000000000000000000000000000000000000000000000000),((-221617647:ℚ)/1024000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((4113860577:ℚ)/5000000000),((5104585411:ℚ)/5000000000),((-3104585411:ℚ)/16200000000),((-4021581731:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((17032446633410933453718663350360941967955967334566343591159:ℚ)/86400000000000000000000000000000000000000000000000000000000),((-221617647:ℚ)/1024000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((126739261:ℚ)/125000000),((14023211837:ℚ)/10000000000),((-10023211837:ℚ)/40000000000),((-172217783:ℚ)/2760000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2489432708410858382922430726069362610515959307049163:ℚ)/10950300000000000000000000000000000000000000000000000),((-221617647:ℚ)/1024000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC13
#check @N11Formalization.C450Source27GroupedC13.bound
#print axioms N11Formalization.C450Source27GroupedC13.valid0
#print axioms N11Formalization.C450Source27GroupedC13.valid1
#print axioms N11Formalization.C450Source27GroupedC13.valid2
#print axioms N11Formalization.C450Source27GroupedC13.valid3
#print axioms N11Formalization.C450Source27GroupedC13.valid4
#print axioms N11Formalization.C450Source27GroupedC13.valid5
#print axioms N11Formalization.C450Source27GroupedC13.valid6
#print axioms N11Formalization.C450Source27GroupedC13.valid7
#print axioms N11Formalization.C450Source27GroupedC13.valid8
#print axioms N11Formalization.C450Source27GroupedC13.valid9
#print axioms N11Formalization.C450Source27GroupedC13.valid10
#print axioms N11Formalization.C450Source27GroupedC13.valid11
#print axioms N11Formalization.C450Source27GroupedC13.valid12
#print axioms N11Formalization.C450Source27GroupedC13.bound
#print axioms N11Formalization.C450Source27GroupedC13.endpoint_checks
