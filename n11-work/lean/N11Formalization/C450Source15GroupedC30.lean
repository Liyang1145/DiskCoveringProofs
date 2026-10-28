import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((2852034871:ℚ)/5000000000),((6245613023:ℚ)/10000000000),((13745484441:ℚ)/17800000000),((48199291161:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7219242877:ℚ)/10000000000),((-4060296896302211869878750002085670189:ℚ)/70496900000000000000000000000000000000),((-4162029389565434292529189527:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6179492107:ℚ)/10000000000),((3241674939:ℚ)/5000000000),((88653397391:ℚ)/110600000000),((24931724573:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((388346167:ℚ)/625000000),((-557049441968961571382481474460189567025226255698617025401:ℚ)/8455618850000000000000000000000000000000000000000000000000),((-1032431936407667637682052223:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((802147687:ℚ)/1250000000),((52508367:ℚ)/78125000),((882147687:ℚ)/1100000000),((57508367:ℚ)/61718750),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((282707821:ℚ)/500000000),((-549151872794697480539480539766800535932995123017017:ℚ)/8318750000000000000000000000000000000000000000000000),((-250085599189519870241607:ℚ)/902500000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6654858289:ℚ)/10000000000),((6839926099:ℚ)/10000000000),((94833157757:ℚ)/116300000000),((52359482693:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2520192523:ℚ)/5000000000),((-171454806379580917372768511082697936276563279070929724803:ℚ)/2457871479687500000000000000000000000000000000000000000000),((-4081230882039379672375353263:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1693423087:ℚ)/2500000000),((6958777839:ℚ)/10000000000),((24094500131:ℚ)/29550000000),((53191444873:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2353232523:ℚ)/5000000000),((-312404812066818331195131062575556727427624902155868101:ℚ)/4479710742187500000000000000000000000000000000000000000),((-4065053321954989159359152823:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3446261851:ℚ)/5000000000),((7018202491:ℚ)/10000000000),((48961404063:ℚ)/59575000000),((53607417437:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4349027663:ℚ)/10000000000),((-94527485743951650205234529972003020523473385753222888817:ℚ)/1321515223339843750000000000000000000000000000000000000000),((-4056962290815190485072635903:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1390387681:ℚ)/2000000000),((1769406589:ℚ)/2500000000),((19739039853:ℚ)/24020000000),((13505846123:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((4159602453:ℚ)/10000000000),((-387076257297223199400052722419506837112014272920145387:ℚ)/5413511253125000000000000000000000000000000000000000000),((-253054359726675143861767823:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((43820953:ℚ)/62500000),((7137049453:ℚ)/10000000000),((621672389:ℚ)/756562500),((54439346171:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3961682593:ℚ)/10000000000),((-7164800791755783455526433864949236400707583859277:ℚ)/100242222404479980468750000000000000000000000000000),((-4040775713865585215619256367:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((353538297:ℚ)/500000000),((35982359:ℚ)/50000000),((5011997861:ℚ)/6100000000),((274276513:ℚ)/302625000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3753920879:ℚ)/10000000000),((-101359201697861660871328426863428780436838204942083571:ℚ)/1418631250000000000000000000000000000000000000000000000),((-100817004078537236063303:ℚ)/369664000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7130178801:ℚ)/10000000000),((1451178683:ℚ)/2000000000),((101012324413:ℚ)/122950000000),((11054250781:ℚ)/12200000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((3534578183:ℚ)/10000000000),((-207416683529084993705662682127836107604885669415964266067:ℚ)/2904060269335937500000000000000000000000000000000000000000),((-160983324042500491571323007:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1797397769:ℚ)/2500000000),((3657657157:ℚ)/5000000000),((8482056999:ℚ)/10325000000),((27843600099:ℚ)/30737500000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((3301342701:ℚ)/10000000000),((-491175542436530716952190834500188210526609136280773569:ℚ)/6879394238281250000000000000000000000000000000000000000),((-1004121131376827183430825087:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((362450139:ℚ)/500000000),((743415403:ℚ)/1000000000),((5127851807:ℚ)/6290000000),((807415403:ℚ)/885000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((305102541:ℚ)/1000000000),((-105821964317470463671819207638321662790757451340217:ℚ)/1518909844970703125000000000000000000000000000000000),((-40002828252014439432367967:ℚ)/147865600000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((3683912261:ℚ)/5000000000),((7671825561:ℚ)/10000000000),((52050859393:ℚ)/64800000000),((58182778927:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1239076857:ℚ)/5000000000),((-1394840377040383965953651375274664099738971756481635103:ℚ)/20995200000000000000000000000000000000000000000000000000),((-275461349:ℚ)/1024000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((7605461689:ℚ)/10000000000),((9572904259:ℚ)/10000000000),((107191001957:ℚ)/160000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-55679864377093560422542639248966152572150260151109095027:ℚ)/1600000000000000000000000000000000000000000000000000000000),((-275461349:ℚ)/1024000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((4753162161:ℚ)/5000000000),((13374170117:ℚ)/10000000000),((65951108093:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1909244093207952100729591794832133203:ℚ)/112131072000000000000000000000000000000),((-275461349:ℚ)/1024000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC30
#check @N11Formalization.C450Source15GroupedC30.bound
#print axioms N11Formalization.C450Source15GroupedC30.valid0
#print axioms N11Formalization.C450Source15GroupedC30.valid1
#print axioms N11Formalization.C450Source15GroupedC30.valid2
#print axioms N11Formalization.C450Source15GroupedC30.valid3
#print axioms N11Formalization.C450Source15GroupedC30.valid4
#print axioms N11Formalization.C450Source15GroupedC30.valid5
#print axioms N11Formalization.C450Source15GroupedC30.valid6
#print axioms N11Formalization.C450Source15GroupedC30.valid7
#print axioms N11Formalization.C450Source15GroupedC30.valid8
#print axioms N11Formalization.C450Source15GroupedC30.valid9
#print axioms N11Formalization.C450Source15GroupedC30.valid10
#print axioms N11Formalization.C450Source15GroupedC30.valid11
#print axioms N11Formalization.C450Source15GroupedC30.valid12
#print axioms N11Formalization.C450Source15GroupedC30.valid13
#print axioms N11Formalization.C450Source15GroupedC30.valid14
#print axioms N11Formalization.C450Source15GroupedC30.bound
#print axioms N11Formalization.C450Source15GroupedC30.endpoint_checks
