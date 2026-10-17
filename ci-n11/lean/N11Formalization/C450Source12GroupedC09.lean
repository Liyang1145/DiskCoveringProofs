import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((795569717:ℚ)/1250000000),((6646212437:ℚ)/10000000000),((-5846212437:ℚ)/12400000000),((-4688988019:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5782108507:ℚ)/10000000000),((945602081237238043518507226609383780736023577431552267:ℚ)/25844220733642578125000000000000000000000000000000000000),((375783158861663459617383:ℚ)/2888000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((6602443599:ℚ)/10000000000),((3442057361:ℚ)/5000000000),((-3042057361:ℚ)/6437500000),((-39177105193:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5181385793:ℚ)/10000000000),((49650020483220074389834741011117883988025438563720844697:ℚ)/1361471381250000000000000000000000000000000000000000000000),((93121319711963208111647:ℚ)/722000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6840301941:ℚ)/10000000000),((1750763823:ℚ)/2500000000),((-1550763823:ℚ)/3337500000),((-40842113587:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4509356587:ℚ)/10000000000),((4752744688810997204880345128233762267309626691868482380863:ℚ)/133955308320703125000000000000000000000000000000000000000000),((69201067732821047772709:ℚ)/541500000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6959221697:ℚ)/10000000000),((1412504619:ℚ)/2000000000),((-1252504619:ℚ)/2717500000),((-13891517293:ℚ)/36550000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4135821451:ℚ)/10000000000),((181486640181401051944228866678154978540006940579363714477:ℚ)/5183125580041503906250000000000000000000000000000000000000),((44084018565327162470581:ℚ)/346560000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((1754669841:ℚ)/2500000000),((7121989299:ℚ)/10000000000),((-6321989299:ℚ)/13706250000),((-10522688887:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1968312201:ℚ)/5000000000),((9904977380022259311593339854490679086966078832406414313:ℚ)/282946352204132080078125000000000000000000000000000000000),((1099636238587542303019621:ℚ)/8664000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((7078135607:ℚ)/10000000000),((1430344363:ℚ)/2000000000),((-1270344363:ℚ)/2765000000),((-14168983083:ℚ)/37025000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((745476641:ℚ)/2000000000),((95342165600825720301451537764663754815655169537450438613:ℚ)/2741008461720275878906250000000000000000000000000000000000),((14627726055339434314983:ℚ)/115520000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7107863207:ℚ)/10000000000),((7181453947:ℚ)/10000000000),((-6381453947:ℚ)/13884375000),((-42715042449:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((904613393:ℚ)/2500000000),((5236804211564930806247227639072106076312053020067199777469:ℚ)/150565367716104125976562500000000000000000000000000000000000),((365282790054700335072263:ℚ)/2888000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((1427518093:ℚ)/2000000000),((7211185699:ℚ)/10000000000),((-6411185699:ℚ)/13943750000),((-8584626651:ℚ)/22405000000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3506295947:ℚ)/10000000000),((13635232795496995703659439014648383583584562124547026627:ℚ)/392061720168107421875000000000000000000000000000000000000),((364872563646953859403607:ℚ)/2888000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((1433463477:ℚ)/2000000000),((7240917077:ℚ)/10000000000),((-6440917077:ℚ)/14003125000),((-8626244339:ℚ)/22500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((135623579:ℚ)/400000000),((902810394966162481490098819670610828470836495419964439:ℚ)/25960993766784667968750000000000000000000000000000000000),((364462472102213296496103:ℚ)/2888000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((7197043971:ℚ)/10000000000),((1454129617:ℚ)/2000000000),((-431376539:ℚ)/937500000),((-43339307797:ℚ)/112975000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3270957021:ℚ)/10000000000),((58758533965403257052511204162192323221977730479608924593:ℚ)/1689772894757080078125000000000000000000000000000000000000),((14562100614416331479423:ℚ)/115520000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((1806692557:ℚ)/2500000000),((912547341:ℚ)/1250000000),((-812547341:ℚ)/1765234375),((-10886847899:ℚ)/28362500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3146950301:ℚ)/10000000000),((3500951930201081208022797209553871529523929930388434827:ℚ)/100687581980840682983398437500000000000000000000000000000),((17045751250675974257101:ℚ)/135375000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((7256496159:ℚ)/10000000000),((919979867:ℚ)/1250000000),((-819979867:ℚ)/1772656250),((-3977770283:ℚ)/10400000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1509014791:ℚ)/5000000000),((34869703411339013788979377693992180130461200212603132489:ℚ)/996998600000000000000000000000000000000000000000000000000),((298737811300172830667:ℚ)/2375000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((914493383:ℚ)/1250000000),((3709648869:ℚ)/5000000000),((-3309648869:ℚ)/7150000000),((-5521453681:ℚ)/14418750000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((548529343:ℚ)/2000000000),((38119472638826050960571800656244010655950766898811:ℚ)/1090153596891090273857116699218750000000000000000000),((271834850480904508394581:ℚ)/2166000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1475079343:ℚ)/2000000000),((7478755169:ℚ)/10000000000),((-2226251723:ℚ)/4806250000),((-8917555401:ℚ)/23260000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((121860137:ℚ)/500000000),((132154471441680860977153636376228158473180417011716640663:ℚ)/3780206335759375000000000000000000000000000000000000000000),((361628294073396840767327:ℚ)/2888000000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((1486969029:ℚ)/2000000000),((3798833023:ℚ)/5000000000),((-3398833023:ℚ)/7268750000),((-9000783203:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2088543353:ℚ)/10000000000),((1964338231458119509415701788812067725273138071363450989:ℚ)/55572304993750000000000000000000000000000000000000000000),((90219237751108039298303:ℚ)/722000000000000000000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((7553738457:ℚ)/10000000000),((7835472739:ℚ)/10000000000),((-7035472739:ℚ)/14775000000),((-45836169199:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((220784611:ℚ)/2000000000),((247967773183959983520734066685058091714273659833315650227:ℚ)/6872221875000000000000000000000000000000000000000000000000),((1890067361539573:ℚ)/15200000000000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((3895755833:ℚ)/5000000000),((332441283:ℚ)/400000000),((-300441283:ℚ)/610000000),((-23750290831:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((8983337909431782158741640466454119513021570380340611839:ℚ)/240132600000000000000000000000000000000000000000000000000),((248217:ℚ)/2000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((4133504973:ℚ)/5000000000),((2042547473:ℚ)/2000000000),((-1882547473:ℚ)/3240000000),((-25414534811:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((714509587147396189453648422071623547174707316927879667773:ℚ)/16200000000000000000000000000000000000000000000000000000000),((248217:ℚ)/2000000)⟩
theorem valid17 : Valid source12 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((5084264577:ℚ)/5000000000),((1401473813:ℚ)/1000000000),((-1321473813:ℚ)/2000000000),((-1394341393:ℚ)/4800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((182997972498605311686221358108169056475844014552877:ℚ)/3600000000000000000000000000000000000000000000000000),((248217:ℚ)/2000000)⟩
theorem valid18 : Valid source12 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4443:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC09
#check @N11Formalization.C450Source12GroupedC09.bound
#print axioms N11Formalization.C450Source12GroupedC09.valid0
#print axioms N11Formalization.C450Source12GroupedC09.valid1
#print axioms N11Formalization.C450Source12GroupedC09.valid2
#print axioms N11Formalization.C450Source12GroupedC09.valid3
#print axioms N11Formalization.C450Source12GroupedC09.valid4
#print axioms N11Formalization.C450Source12GroupedC09.valid5
#print axioms N11Formalization.C450Source12GroupedC09.valid6
#print axioms N11Formalization.C450Source12GroupedC09.valid7
#print axioms N11Formalization.C450Source12GroupedC09.valid8
#print axioms N11Formalization.C450Source12GroupedC09.valid9
#print axioms N11Formalization.C450Source12GroupedC09.valid10
#print axioms N11Formalization.C450Source12GroupedC09.valid11
#print axioms N11Formalization.C450Source12GroupedC09.valid12
#print axioms N11Formalization.C450Source12GroupedC09.valid13
#print axioms N11Formalization.C450Source12GroupedC09.valid14
#print axioms N11Formalization.C450Source12GroupedC09.valid15
#print axioms N11Formalization.C450Source12GroupedC09.valid16
#print axioms N11Formalization.C450Source12GroupedC09.valid17
#print axioms N11Formalization.C450Source12GroupedC09.valid18
#print axioms N11Formalization.C450Source12GroupedC09.bound
#print axioms N11Formalization.C450Source12GroupedC09.endpoint_checks
