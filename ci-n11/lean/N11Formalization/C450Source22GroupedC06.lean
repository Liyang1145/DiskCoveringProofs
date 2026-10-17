import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6668468203:ℚ)/10000000000),((6866737461:ℚ)/10000000000),((-62734112071:ℚ)/99200000000),((-5324468203:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5003180701:ℚ)/10000000000),((15375939505655076037357687505585742946157595582473647607269343:ℚ)/100583247974400000000000000000000000000000000000000000000000000),((2785119452959262243681938767:ℚ)/7393280000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((1696953433:ℚ)/2500000000),((6986034351:ℚ)/10000000000),((-64046377861:ℚ)/101100000000),((-1360953433:ℚ)/2575000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4665323281:ℚ)/10000000000),((15720456254259809397728105365929032229554735447743086822884129:ℚ)/102777770508553125000000000000000000000000000000000000000000000),((173487687407292372990536407:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((6907137131:ℚ)/10000000000),((7045675249:ℚ)/10000000000),((-64702427739:ℚ)/103000000000),((-5563137131:ℚ)/10395000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4303163361:ℚ)/10000000000),((78879220663446289815461601268779026874584590313928485405396699:ℚ)/527123821563281250000000000000000000000000000000000000000000000),((2766359038559448318596862543:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1393358183:ℚ)/2000000000),((3552655649:ℚ)/5000000000),((-518717653:ℚ)/825000000),((-1124558183:ℚ)/2098000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((205548477:ℚ)/500000000),((72271555248869984618208963704171521404494315194448347651:ℚ)/482728402551269531250000000000000000000000000000000000000),((110463569429338760003224407:ℚ)/295731200000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3513219807:ℚ)/5000000000),((895617829:ℚ)/1250000000),((-8251796119:ℚ)/13112500000),((-2841219807:ℚ)/5292500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((48873977:ℚ)/125000000),((64787687338582414476084403498825372181022799019859317820129:ℚ)/432539108911480712890625000000000000000000000000000000000000),((2067590660197162397950723861:ℚ)/5544960000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3543041683:ℚ)/5000000000),((7194756569:ℚ)/10000000000),((-66342322259:ℚ)/105850000000),((-2871041683:ℚ)/5316250000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3698560509:ℚ)/10000000000),((9935272430409325524544562722604342973828887910854615552739706477:ℚ)/67036815295923639453125000000000000000000000000000000000000000000),((687988492296274232964517407:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((711590343:ℚ)/1000000000),((225767793:ℚ)/312500000),((-2083445723:ℚ)/3322656250),((-192396781:ℚ)/356000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((224278113:ℚ)/625000000),((4307484127820410658040429907320551536921755723542745686417:ℚ)/29056028477483606338500976562500000000000000000000000000000),((82485756628574045830139461:ℚ)/221798400000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3572861153:ℚ)/5000000000),((1450876213:ℚ)/2000000000),((-13399638343:ℚ)/21360000000),((-2900861153:ℚ)/5363750000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3475011799:ℚ)/10000000000),((185608599286352950270915885605242750603480242427294197801727:ℚ)/1251678469360725000000000000000000000000000000000000000000000),((686772124870897931466751367:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((7175540011:ℚ)/10000000000),((7284191653:ℚ)/10000000000),((-67326108183:ℚ)/107275000000),((-5831540011:ℚ)/10775000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1678954339:ℚ)/5000000000),((415221911549168552919651872971300645324642370264162194456689:ℚ)/2799369111865831565856933593750000000000000000000000000000000),((2744643804346890193434691023:ℚ)/7393280000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7205356561:ℚ)/10000000000),((7314001153:ℚ)/10000000000),((-67654012683:ℚ)/107750000000),((-5861356561:ℚ)/10822500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((809185511:ℚ)/2500000000),((679342668014291371870369131302702121468979225911970366687577581:ℚ)/4578856648317965698242187500000000000000000000000000000000000000),((2742191135174740511811926823:ℚ)/7393280000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((723517197:ℚ)/1000000000),((7343809581:ℚ)/10000000000),((-67981905391:ℚ)/108225000000),((-589117197:ℚ)/1087000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((777759127:ℚ)/2500000000),((6257624869943762910540208643490090347706942041911815238323343:ℚ)/42166632075538623046875000000000000000000000000000000000000000),((82191914752424795194892701:ℚ)/221798400000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1452997251:ℚ)/2000000000),((296136931:ℚ)/400000000),((-2745506241:ℚ)/4348000000),((-394732417:ℚ)/731000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((29802171:ℚ)/100000000),((5148240936729190992047227491080967989464750404565063257447:ℚ)/34315741727429150000000000000000000000000000000000000000000),((328471424829780490782059389:ℚ)/887193600000000000000000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((1831152877:ℚ)/2500000000),((7463032843:ℚ)/10000000000),((-23097787091:ℚ)/36550000000),((-1495152877:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1350116673:ℚ)/5000000000),((46894263480906548470928710602283976775964568493708948349153:ℚ)/312468087233587646484375000000000000000000000000000000000000),((170768794505734030939165727:ℚ)/462080000000000000000000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((1476846487:ℚ)/2000000000),((7582240027:ℚ)/10000000000),((-70604640297:ℚ)/110600000000),((-1208046487:ℚ)/2250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((298568627:ℚ)/1250000000),((204949055481618433438505690633992196212939418185471420831:ℚ)/1337705325878906250000000000000000000000000000000000000000),((109092305930124603885016247:ℚ)/295731200000000000000000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((7503461753:ℚ)/10000000000),((385071597:ℚ)/500000000),((-3595787567:ℚ)/5625000000),((-6159461753:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((398895103:ℚ)/2500000000),((1742727468216528460635872032283835983510236760576436145849:ℚ)/11373383331298828125000000000000000000000000000000000000000),((2717225804004562754558838167:ℚ)/7393280000000000000000000000)⟩
theorem valid14 : Valid source22 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7622675057:ℚ)/10000000000),((4327249297:ℚ)/5000000000),((-41199742267:ℚ)/57200000000),((-6278675057:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((18978299971674639545245111596105704753375994039706338869819:ℚ)/98388318600000000000000000000000000000000000000000000000000),((187601673:ℚ)/512000000)⟩
theorem valid15 : Valid source22 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8575890041:ℚ)/10000000000),((1319859747:ℚ)/1250000000),((-12918457217:ℚ)/16200000000),((-7231890041:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((9004525679623770388990771854163044118623782617051026133:ℚ)/39858075000000000000000000000000000000000000000000000000),((187601673:ℚ)/512000000)⟩
theorem valid16 : Valid source22 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((2620120237:ℚ)/2500000000),((14364011753:ℚ)/10000000000),((-145204129283:ℚ)/160000000000),((-2284120237:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((698549681736145881499639277388132906414247:ℚ)/2437632000000000000000000000000000000000000),((187601673:ℚ)/512000000)⟩
theorem valid17 : Valid source22 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC06
#check @N11Formalization.C450Source22GroupedC06.bound
#print axioms N11Formalization.C450Source22GroupedC06.valid0
#print axioms N11Formalization.C450Source22GroupedC06.valid1
#print axioms N11Formalization.C450Source22GroupedC06.valid2
#print axioms N11Formalization.C450Source22GroupedC06.valid3
#print axioms N11Formalization.C450Source22GroupedC06.valid4
#print axioms N11Formalization.C450Source22GroupedC06.valid5
#print axioms N11Formalization.C450Source22GroupedC06.valid6
#print axioms N11Formalization.C450Source22GroupedC06.valid7
#print axioms N11Formalization.C450Source22GroupedC06.valid8
#print axioms N11Formalization.C450Source22GroupedC06.valid9
#print axioms N11Formalization.C450Source22GroupedC06.valid10
#print axioms N11Formalization.C450Source22GroupedC06.valid11
#print axioms N11Formalization.C450Source22GroupedC06.valid12
#print axioms N11Formalization.C450Source22GroupedC06.valid13
#print axioms N11Formalization.C450Source22GroupedC06.valid14
#print axioms N11Formalization.C450Source22GroupedC06.valid15
#print axioms N11Formalization.C450Source22GroupedC06.valid16
#print axioms N11Formalization.C450Source22GroupedC06.valid17
#print axioms N11Formalization.C450Source22GroupedC06.bound
#print axioms N11Formalization.C450Source22GroupedC06.endpoint_checks
