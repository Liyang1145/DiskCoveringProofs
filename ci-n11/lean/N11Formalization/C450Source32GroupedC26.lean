import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((9:ℚ)/16),((5:ℚ)/8),((267448567:ℚ)/500000000),((5685584193:ℚ)/10000000000),((3367037103:ℚ)/5150000000),((7669584193:ℚ)/9920000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7900468733:ℚ)/10000000000),((-12810500146008845160193790409179756018693118913361322309047:ℚ)/38836558110720000000000000000000000000000000000000000000000),((-3300243315697746019312321301:ℚ)/7393280000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5589309171:ℚ)/10000000000),((296292611:ℚ)/500000000),((23167927513:ℚ)/35600000000),((395492611:ℚ)/515000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((930609097:ℚ)/1250000000),((-111182950029697850959066019248063013057058855254496863:ℚ)/338105100273437500000000000000000000000000000000000000),((-8148248779573360484941629:ℚ)/18483200000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1165888337:ℚ)/2000000000),((1209182489:ℚ)/2000000000),((14332995033:ℚ)/21740000000),((1605982489:ℚ)/2136000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6965942363:ℚ)/10000000000),((-1613456338344171363291189008161119922265303443172204104831:ℚ)/4797904414239360000000000000000000000000000000000000000000),((-129847876191753479807013829:ℚ)/295731200000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((5949437823:ℚ)/10000000000),((1541481733:ℚ)/2500000000),((72744940407:ℚ)/110600000000),((2037481733:ℚ)/2717500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3358050779:ℚ)/5000000000),((-30167445819416896951566045421055307980146793387272970707:ℚ)/89898040033018569946289062500000000000000000000000000000),((-201516106005452279656197261:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((6069390493:ℚ)/10000000000),((1257179609:ℚ)/2000000000),((24608171479:ℚ)/37500000000),((1653979609:ℚ)/2212000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6458241597:ℚ)/10000000000),((-7584968792184948171925785142190149481829323288473:ℚ)/22648979062500000000000000000000000000000000000000),((-128069338013199250972768069:ℚ)/295731200000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6189301941:ℚ)/10000000000),((6405827991:ℚ)/10000000000),((74903717469:ℚ)/114400000000),((8389827991:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((247653251:ℚ)/400000000),((-12164553670978388007846793254494832187088657985623055014027:ℚ)/36394826660156250000000000000000000000000000000000000000000),((-3178624382525268365577904869:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6309174261:ℚ)/10000000000),((261028753:ℚ)/400000000),((75982568349:ℚ)/116300000000),((340388753:ℚ)/457600000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((147852893:ℚ)/250000000),((-4913346148536403623186468605560457588218368028313885391:ℚ)/14727695779962880000000000000000000000000000000000000000),((-5047889110820081937119541:ℚ)/11829248000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3214504703:ℚ)/5000000000),((664557247:ℚ)/1000000000),((12843514109:ℚ)/19700000000),((862957247:ℚ)/1163000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5625041423:ℚ)/10000000000),((-6353088588347305380206735569184647651808161343249259171:ℚ)/19077506851038437500000000000000000000000000000000000000),((-31306525727870907734475541:ℚ)/73932800000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6548809201:ℚ)/10000000000),((3382695361:ℚ)/5000000000),((78139282809:ℚ)/120100000000),((1458231787:ℚ)/1970000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2661072807:ℚ)/5000000000),((-3436961013312963127627538799626473390926772116294887988437:ℚ)/10338462806787187500000000000000000000000000000000000000000),((-776447548447349926512068629:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((833571919:ℚ)/1250000000),((1377035053:ℚ)/2000000000),((9902147271:ℚ)/15250000000),((1773835053:ℚ)/2402000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((625360849:ℚ)/1250000000),((-21394250784629360369575345786195904024940673619860123761:ℚ)/64459761193210000000000000000000000000000000000000000000),((-123213748837254470540291741:ℚ)/295731200000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3394154729:ℚ)/5000000000),((3562324717:ℚ)/5000000000),((40147392561:ℚ)/62900000000),((4554324717:ℚ)/6100000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((466387291:ℚ)/1000000000),((-9109031875471543143845417531790029175693807534619157455761:ℚ)/28063434319062500000000000000000000000000000000000000000000),((-754868588229363068211410461:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((1405537487:ℚ)/2000000000),((7364006471:ℚ)/10000000000),((5496612461:ℚ)/8640000000),((9348006471:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((390560773:ℚ)/1000000000),((-5294597528662123014862161915781172192297686839111190037:ℚ)/16343929710000000000000000000000000000000000000000000000),((-2964498994606508872821039109:ℚ)/7393280000000000000000000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7266954051:ℚ)/10000000000),((1159457441:ℚ)/1250000000),((84602586459:ℚ)/160000000000),((1407457441:ℚ)/1620000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1485693239:ℚ)/5000000000),((-239366197759738080073473152938846512202392366960089:ℚ)/996451875000000000000000000000000000000000000000000),((-47832389665132437:ℚ)/121600000000000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((917804099:ℚ)/1000000000),((13089288033:ℚ)/10000000000),((3393412297:ℚ)/7360000000),((15073288033:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-18911891322712011274087649001756452527:ℚ)/108339200000000000000000000000000000000),((-40596851:ℚ)/102400000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC26
#check @N11Formalization.C450Source32GroupedC26.bound
#print axioms N11Formalization.C450Source32GroupedC26.valid0
#print axioms N11Formalization.C450Source32GroupedC26.valid1
#print axioms N11Formalization.C450Source32GroupedC26.valid2
#print axioms N11Formalization.C450Source32GroupedC26.valid3
#print axioms N11Formalization.C450Source32GroupedC26.valid4
#print axioms N11Formalization.C450Source32GroupedC26.valid5
#print axioms N11Formalization.C450Source32GroupedC26.valid6
#print axioms N11Formalization.C450Source32GroupedC26.valid7
#print axioms N11Formalization.C450Source32GroupedC26.valid8
#print axioms N11Formalization.C450Source32GroupedC26.valid9
#print axioms N11Formalization.C450Source32GroupedC26.valid10
#print axioms N11Formalization.C450Source32GroupedC26.valid11
#print axioms N11Formalization.C450Source32GroupedC26.valid12
#print axioms N11Formalization.C450Source32GroupedC26.valid13
#print axioms N11Formalization.C450Source32GroupedC26.bound
#print axioms N11Formalization.C450Source32GroupedC26.endpoint_checks
