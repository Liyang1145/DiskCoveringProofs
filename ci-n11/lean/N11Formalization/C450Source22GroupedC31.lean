import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5405605539:ℚ)/10000000000),((238550183:ℚ)/400000000),((44239238773:ℚ)/53400000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((487188569:ℚ)/625000000),((-404386851076432217244486348111931265413:ℚ)/1903416300000000000000000000000000000000),((-923372264657058464420730857:ℚ)/2772480000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1176219329:ℚ)/2000000000),((1550410391:ℚ)/2500000000),((9513535303:ℚ)/11060000000),((1774410391:ℚ)/1780000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((857416093:ℚ)/1250000000),((-3035154223334402740002443120545768263794378248008221963:ℚ)/12683428275000000000000000000000000000000000000000000000),((-12040164285734358428658699:ℚ)/36966400000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((1529704213:ℚ)/2500000000),((6320575233:ℚ)/10000000000),((12307929491:ℚ)/14062500000),((3092817957:ℚ)/3160000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6349396717:ℚ)/10000000000),((-25668522510599512550244790302631794941784018604698631:ℚ)/101840123534202575683593750000000000000000000000000000),((-18601122296447994748844091:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((623767137:ℚ)/1000000000),((3219751393:ℚ)/5000000000),((5006369959:ℚ)/5720000000),((3667751393:ℚ)/3750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((95012549:ℚ)/156250000),((-147234991068648016278640331491462624165425717808713633:ℚ)/584841400000000000000000000000000000000000000000000000),((-8825270880930809532823073:ℚ)/27724800000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6356522411:ℚ)/10000000000),((3279212263:ℚ)/5000000000),((50895656877:ℚ)/58150000000),((11181636789:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1450356343:ℚ)/2500000000),((-154526482433398042508400986897265436599955763300335575539:ℚ)/614467869921875000000000000000000000000000000000000000000),((-290734753800204064941887219:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((6475370147:ℚ)/10000000000),((827235413:ℚ)/1250000000),((51727591029:ℚ)/58625000000),((2817706239:ℚ)/2907500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5509599273:ℚ)/10000000000),((-162124504929905245273360425257677714289488970269366866987:ℚ)/629649102783203125000000000000000000000000000000000000000),((-289045931431861605265308451:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((3267396413:ℚ)/5000000000),((6677340733:ℚ)/10000000000),((26071774891:ℚ)/29550000000),((3245717457:ℚ)/3350000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5358378419:ℚ)/10000000000),((-1728935590712557204381616760816910381034082127932837359:ℚ)/6719566113281250000000000000000000000000000000000000000),((-71831641381255901586149891:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6594214737:ℚ)/10000000000),((1684199211:ℚ)/2500000000),((52559503159:ℚ)/59575000000),((1908199211:ℚ)/1970000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5203206033:ℚ)/10000000000),((-509682817207196434439876596467363428272565713118954283371:ℚ)/1982272835009765625000000000000000000000000000000000000000),((-856822575747328687614263873:ℚ)/2772480000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((66536359:ℚ)/100000000),((679625167:ℚ)/1000000000),((529754513:ℚ)/600500000),((2307675501:ℚ)/2383000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((630464289:ℚ)/1250000000),((-130405844593740797574686163206159623655438955275077:ℚ)/507516679980468750000000000000000000000000000000000),((-28388880963207495579659:ℚ)/92416000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6713056331:ℚ)/10000000000),((171392631:ℚ)/250000000),((17797131439:ℚ)/20175000000),((581377893:ℚ)/600500000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((609934571:ℚ)/1250000000),((-4942193523212353992867948332603709518269360395011074979:ℚ)/19246506701660156250000000000000000000000000000000000000),((-282170417817863570732176179:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((423279753:ℚ)/625000000),((1383031517:ℚ)/2000000000),((3362958271:ℚ)/3812500000),((520743839:ℚ)/538000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4709993099:ℚ)/10000000000),((-133321571343977813155851725524808856211617782914893731:ℚ)/519518280029296875000000000000000000000000000000000000),((-6573101927178224995437181:ℚ)/21660000000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6831895069:ℚ)/10000000000),((6974608731:ℚ)/10000000000),((54223265483:ℚ)/61475000000),((23611826193:ℚ)/24400000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((283417027:ℚ)/625000000),((-11637706739900289137889374182888205318938826109648919981:ℚ)/45375941708374023437500000000000000000000000000000000000),((-278734602091339574100530979:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((26919193:ℚ)/39062500),((1758514677:ℚ)/2500000000),((426868702:ℚ)/483984375),((5947544031:ℚ)/6147500000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((34822447:ℚ)/80000000),((-181621864595027521963661539122246952848761085810133:ℚ)/708555772528052330017089843750000000000000000000000),((-541049172905140827118733:ℚ)/1805000000000000000000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((3475365541:ℚ)/5000000000),((3576477629:ℚ)/5000000000),((27527558787:ℚ)/31450000000),((4024477629:ℚ)/4130000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((166541287:ℚ)/400000000),((-6086222997289285812571268207599652985842493911859563829:ℚ)/24302557519531250000000000000000000000000000000000000000),((-68387386953048204211955859:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((3534782247:ℚ)/5000000000),((1478147089:ℚ)/2000000000),((27943475729:ℚ)/32400000000),((4972041267:ℚ)/5032000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((939557569:ℚ)/2500000000),((-942593350281408361683217904475303072084303116558034869:ℚ)/3936600000000000000000000000000000000000000000000000000),((-199961648296898845714871153:ℚ)/693120000000000000000000000)⟩
theorem valid14 : Valid source22 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((3653611987:ℚ)/5000000000),((3933124591:ℚ)/5000000000),((28775283909:ℚ)/34300000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((278471087:ℚ)/1000000000),((-1734625088826172522831107401292273665633663057766790123:ℚ)/7881563867187500000000000000000000000000000000000000000),((-65148100811086162369372291:ℚ)/231040000000000000000000000)⟩
theorem valid15 : Valid source22 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((3891258203:ℚ)/5000000000),((521356807:ℚ)/625000000),((30438807421:ℚ)/36200000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),(0:ℚ),((-1313880743110819761917844153353443854067459621470657323:ℚ)/5929741000000000000000000000000000000000000000000000000),((-36117717:ℚ)/128000000)⟩
theorem valid16 : Valid source22 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source22 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((2064444529:ℚ)/2500000000),((2323124297:ℚ)/2500000000),((16051111703:ℚ)/20000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-1200230175191801030687513847971141766530685411788794089:ℚ)/6250000000000000000000000000000000000000000000000000000),((-36117717:ℚ)/128000000)⟩
theorem valid17 : Valid source22 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source22 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((9208226897:ℚ)/10000000000),((13094564149:ℚ)/10000000000),((23619196093:ℚ)/36800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-480761003833962197272251868121783297:ℚ)/6229504000000000000000000000000000000),((-36117717:ℚ)/128000000)⟩
theorem valid18 : Valid source22 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source22 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source22 nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((343:ℚ)/400) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source22 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source22 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC31
#check @N11Formalization.C450Source22GroupedC31.bound
#print axioms N11Formalization.C450Source22GroupedC31.valid0
#print axioms N11Formalization.C450Source22GroupedC31.valid1
#print axioms N11Formalization.C450Source22GroupedC31.valid2
#print axioms N11Formalization.C450Source22GroupedC31.valid3
#print axioms N11Formalization.C450Source22GroupedC31.valid4
#print axioms N11Formalization.C450Source22GroupedC31.valid5
#print axioms N11Formalization.C450Source22GroupedC31.valid6
#print axioms N11Formalization.C450Source22GroupedC31.valid7
#print axioms N11Formalization.C450Source22GroupedC31.valid8
#print axioms N11Formalization.C450Source22GroupedC31.valid9
#print axioms N11Formalization.C450Source22GroupedC31.valid10
#print axioms N11Formalization.C450Source22GroupedC31.valid11
#print axioms N11Formalization.C450Source22GroupedC31.valid12
#print axioms N11Formalization.C450Source22GroupedC31.valid13
#print axioms N11Formalization.C450Source22GroupedC31.valid14
#print axioms N11Formalization.C450Source22GroupedC31.valid15
#print axioms N11Formalization.C450Source22GroupedC31.valid16
#print axioms N11Formalization.C450Source22GroupedC31.valid17
#print axioms N11Formalization.C450Source22GroupedC31.valid18
#print axioms N11Formalization.C450Source22GroupedC31.bound
#print axioms N11Formalization.C450Source22GroupedC31.endpoint_checks
