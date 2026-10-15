import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((398132597:ℚ)/625000000),((333078079:ℚ)/500000000),((-743234237:ℚ)/2480000000),((-262132597:ℚ)/1287500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5768699567:ℚ)/10000000000),((44028043426047699059834364723535043810258690156849987:ℚ)/620261297607421875000000000000000000000000000000000000),((42830178231061387498247:ℚ)/577600000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((1652182227:ℚ)/2500000000),((345008371:ℚ)/500000000),((-779025113:ℚ)/2575000000),((-1108182227:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5164662799:ℚ)/10000000000),((864075598124347109825986119571652386798444986101598127:ℚ)/12253242431250000000000000000000000000000000000000000000),((640684207835240658317207:ℚ)/9241600000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6847256951:ℚ)/10000000000),((6854923:ℚ)/9765625),((-31129538:ℚ)/104296875),((-4671256951:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4488312301:ℚ)/10000000000),((590739088560955338024428261894271878342947999121045203991:ℚ)/8573139732525000000000000000000000000000000000000000000000),((9534736265617125787815983:ℚ)/147865600000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((139329877:ℚ)/200000000),((110610487:ℚ)/156250000),((-251831461:ℚ)/849218750),((-95809877:ℚ)/438600000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4111947559:ℚ)/10000000000),((1627759024105362770870359384491936690921598530154291:ℚ)/23883842672831250000000000000000000000000000000000000),((3670254579207423112007:ℚ)/59146240000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((1405221187:ℚ)/2000000000),((285547871:ℚ)/400000000),((-651843613:ℚ)/2193000000),((-970021187:ℚ)/4424000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((782214009:ℚ)/2000000000),((2663703794975412347313097784955597392802537489102829:ℚ)/39120616325000000000000000000000000000000000000000000),((359833474171466418868727:ℚ)/5914624000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((3542856961:ℚ)/5000000000),((7198318087:ℚ)/10000000000),((-16474954261:ℚ)/55300000000),((-2454856961:ℚ)/11155000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((73998101:ℚ)/200000000),((1456986858991810182617308091587096758326099758674068093:ℚ)/21417355929907226562500000000000000000000000000000000000),((2203967604240685428226943:ℚ)/36966400000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((3572658959:ℚ)/5000000000),((7257935213:ℚ)/10000000000),((-16653805639:ℚ)/55775000000),((-828219653:ℚ)/3750000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1738286953:ℚ)/5000000000),((292845594094822937029073642695609692156084811345661243:ℚ)/4308485984802246093750000000000000000000000000000000000),((2158934212368143912856223:ℚ)/36966400000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((900614753:ℚ)/1250000000),((365877413:ℚ)/500000000),((-841632239:ℚ)/2812500000),((-628614753:ℚ)/2836250000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((202409737:ℚ)/625000000),((108947808249426393775328202630806361237348815579251:ℚ)/1604227904983520507812500000000000000000000000000000),((132116185658015237306047:ℚ)/2310400000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((363225717:ℚ)/500000000),((737715733:ℚ)/1000000000),((-1701147199:ℚ)/5672500000),((-19571209:ℚ)/88000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2982331079:ℚ)/10000000000),((327896741604332477695153820617155105307761534884423:ℚ)/4832062400000000000000000000000000000000000000000000),((57305867361452483567:ℚ)/1024000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((7324106959:ℚ)/10000000000),((1874090983:ℚ)/2500000000),((-4342272949:ℚ)/14300000000),((-5148106959:ℚ)/23260000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((540544193:ℚ)/2000000000),((384451011915093876159641390330870538603031346287000898699:ℚ)/5623609945525000000000000000000000000000000000000000000000),((8094330696249029210568223:ℚ)/147865600000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((297731259:ℚ)/400000000),((7615555773:ℚ)/10000000000),((-17726667319:ℚ)/58150000000),((-210691259:ℚ)/945600000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((50857793:ℚ)/250000000),((1941969440779366830704965118562562476045227084786713:ℚ)/28453020156800000000000000000000000000000000000000000),((12372084575896625672423:ℚ)/236584960000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((236326321:ℚ)/312500000),((7853897949:ℚ)/10000000000),((-18441693847:ℚ)/59100000000),((-168326321:ℚ)/762500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((31080421:ℚ)/312500000),((18883352503486982067133747364000565525213261989269631:ℚ)/272920269775390625000000000000000000000000000000000000),((7197363771354431251103:ℚ)/144400000000000000000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((1950181323:ℚ)/2500000000),((8330433427:ℚ)/10000000000),((-325759021:ℚ)/1000000000),((-1406181323:ℚ)/6480000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((20089960129600999354324491819832796397529250340941107:ℚ)/283435200000000000000000000000000000000000000000000000),((12561829:ℚ)/256000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((8277152961:ℚ)/10000000000),((409404459:ℚ)/400000000),((-1023413377:ℚ)/2592000000),((-6101152961:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((661957895875075597871662705725570804766904223483522589883:ℚ)/8294400000000000000000000000000000000000000000000000000000),((12561829:ℚ)/256000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((1018150289:ℚ)/1000000000),((14040594839:ℚ)/10000000000),((-37001784517:ℚ)/80000000000),((-800550289:ℚ)/4416000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((18341649031888627944081656184432556612563492273910601:ℚ)/201835929600000000000000000000000000000000000000000000),((12561829:ℚ)/256000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC11
#check @N11Formalization.C450Source18GroupedC11.bound
#print axioms N11Formalization.C450Source18GroupedC11.valid0
#print axioms N11Formalization.C450Source18GroupedC11.valid1
#print axioms N11Formalization.C450Source18GroupedC11.valid2
#print axioms N11Formalization.C450Source18GroupedC11.valid3
#print axioms N11Formalization.C450Source18GroupedC11.valid4
#print axioms N11Formalization.C450Source18GroupedC11.valid5
#print axioms N11Formalization.C450Source18GroupedC11.valid6
#print axioms N11Formalization.C450Source18GroupedC11.valid7
#print axioms N11Formalization.C450Source18GroupedC11.valid8
#print axioms N11Formalization.C450Source18GroupedC11.valid9
#print axioms N11Formalization.C450Source18GroupedC11.valid10
#print axioms N11Formalization.C450Source18GroupedC11.valid11
#print axioms N11Formalization.C450Source18GroupedC11.valid12
#print axioms N11Formalization.C450Source18GroupedC11.valid13
#print axioms N11Formalization.C450Source18GroupedC11.valid14
#print axioms N11Formalization.C450Source18GroupedC11.bound
#print axioms N11Formalization.C450Source18GroupedC11.endpoint_checks
