import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((5770084777:ℚ)/10000000000),((1261489033:ℚ)/2000000000),((6410084777:ℚ)/8900000000),((18063357429:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7086799303:ℚ)/10000000000),((-177773596009533186509593813972482193:ℚ)/4406056250000000000000000000000000000),((-2391090784576050746605989:ℚ)/9241600000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3122806509:ℚ)/5000000000),((3272602507:ℚ)/5000000000),((10328419527:ℚ)/13825000000),((15567944197:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6062487999:ℚ)/10000000000),((-771172434015354280539844106914198757713784316369134313:ℚ)/16514880566406250000000000000000000000000000000000000000),((-14879099458996793746091949:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((6483349873:ℚ)/10000000000),((6782947573:ℚ)/10000000000),((21370049619:ℚ)/28600000000),((96498318449:ℚ)/110600000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1372377501:ℚ)/2500000000),((-6853748558430370809603857099525383914508264427736732381:ℚ)/146210350000000000000000000000000000000000000000000000000),((-59255330351727187494965229:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6721070971:ℚ)/10000000000),((69018129:ℚ)/100000000),((22083212913:ℚ)/29075000000),((75418129:ℚ)/88000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4856934517:ℚ)/10000000000),((-1909503974435988172702437378387633489359978996047087647:ℚ)/38404241870117187500000000000000000000000000000000000000),((-5912472265069068942741:ℚ)/23104000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3419963047:ℚ)/5000000000),((3510337257:ℚ)/5000000000),((3739963047:ℚ)/4925000000),((49794384341:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((451049121:ℚ)/1000000000),((-9283213518204326436811072689555539959453014588392937:ℚ)/186654614257812500000000000000000000000000000000000000),((-14748516342538175817590949:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((3479388917:ℚ)/5000000000),((1416020797:ℚ)/2000000000),((11398166751:ℚ)/14893750000),((6690756787:ℚ)/7880000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1034318603:ℚ)/2500000000),((-1054953267147152401070647534906845071393378270848328841:ℚ)/20648675364685058593750000000000000000000000000000000000),((-2357148723085882067618109:ℚ)/9241600000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3509101243:ℚ)/5000000000),((446220787:ℚ)/625000000),((11487303729:ℚ)/15012500000),((6320870231:ℚ)/7446875000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3938259937:ℚ)/10000000000),((-67512116307960422376936045773988422597103696987756279:ℚ)/1321658020782470703125000000000000000000000000000000000),((-229934993439283920223269:ℚ)/902500000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((7077626351:ℚ)/10000000000),((7198960357:ℚ)/10000000000),((2572542117:ℚ)/3362500000),((101906484641:ℚ)/120100000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((372922279:ℚ)/1000000000),((-12135248892939396632167514920923780983989932972522123:ℚ)/237611193847656250000000000000000000000000000000000000),((-58797986076463525829414349:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((892131181:ℚ)/1250000000),((7258387299:ℚ)/10000000000),((2916393543:ℚ)/3812500000),((102679034887:ℚ)/121050000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3508367811:ℚ)/10000000000),((-17685125466773543553717970128673976677293188119240497:ℚ)/346345520019531250000000000000000000000000000000000000),((-58732601324830736555253501:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1439294359:ℚ)/2000000000),((7317813437:ℚ)/10000000000),((4701883077:ℚ)/6147500000),((103451574681:ℚ)/122000000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((1636649717:ℚ)/5000000000),((-18532271264502629575371696988434033921768556690771203:ℚ)/363007533666992187500000000000000000000000000000000000),((-58667204045204312557111869:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((725589341:ℚ)/1000000000),((737723879:ℚ)/1000000000),((789589341:ℚ)/1032500000),((10422410427:ℚ)/12295000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((3020696603:ℚ)/10000000000),((-351135996432333930328287678575000457529123448674731:ℚ)/6879394238281250000000000000000000000000000000000000),((-586017942172130899188741:ℚ)/2310400000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((7315314309:ℚ)/10000000000),((1874021803:ℚ)/2500000000),((23865942927:ℚ)/31450000000),((26442283439:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((549143817:ℚ)/2000000000),((-9448262877990722365887337714214700622148108216536737:ℚ)/189863730621337890625000000000000000000000000000000000),((-3654433552504508927333709:ℚ)/14440000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((297366161:ℚ)/400000000),((7733775389:ℚ)/10000000000),((35885129:ℚ)/48000000),((108859080057:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((26161559:ℚ)/125000000),((-3637797502005883656239549034614786227028207399:ℚ)/76800000000000000000000000000000000000000000000),((-1616523:ℚ)/6400000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((1917956389:ℚ)/2500000000),((2408739683:ℚ)/2500000000),((6233869167:ℚ)/10000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-9207703240546402359610219822897567786119853875313017:ℚ)/390625000000000000000000000000000000000000000000000000),((-1616523:ℚ)/6400000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((4786452127:ℚ)/5000000000),((2687269469:ℚ)/2000000000),((5106452127:ℚ)/9200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1812028059439424345071846489585251:ℚ)/194672000000000000000000000000000000),((-1616523:ℚ)/6400000)⟩
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
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
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
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC29
#check @N11Formalization.C450Source14GroupedC29.bound
#print axioms N11Formalization.C450Source14GroupedC29.valid0
#print axioms N11Formalization.C450Source14GroupedC29.valid1
#print axioms N11Formalization.C450Source14GroupedC29.valid2
#print axioms N11Formalization.C450Source14GroupedC29.valid3
#print axioms N11Formalization.C450Source14GroupedC29.valid4
#print axioms N11Formalization.C450Source14GroupedC29.valid5
#print axioms N11Formalization.C450Source14GroupedC29.valid6
#print axioms N11Formalization.C450Source14GroupedC29.valid7
#print axioms N11Formalization.C450Source14GroupedC29.valid8
#print axioms N11Formalization.C450Source14GroupedC29.valid9
#print axioms N11Formalization.C450Source14GroupedC29.valid10
#print axioms N11Formalization.C450Source14GroupedC29.valid11
#print axioms N11Formalization.C450Source14GroupedC29.valid12
#print axioms N11Formalization.C450Source14GroupedC29.valid13
#print axioms N11Formalization.C450Source14GroupedC29.valid14
#print axioms N11Formalization.C450Source14GroupedC29.bound
#print axioms N11Formalization.C450Source14GroupedC29.endpoint_checks
