import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((1602460573:ℚ)/2500000000),((209350189:ℚ)/312500000),((-176850189:ℚ)/387500000),((-8977224011:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5672155249:ℚ)/10000000000),((177306347763219348794032801186314902221096299097643612339:ℚ)/3308060253906250000000000000000000000000000000000000000000),((140827241032002699535377973:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((13295991:ℚ)/20000000),((1363657663:ℚ)/2000000000),((-1155657663:ℚ)/2575000000),((-75151937:ℚ)/209800000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5059050423:ℚ)/10000000000),((77307426564887384620074080928957176625117136128049:ℚ)/1486187835587500000000000000000000000000000000000000),((24610048146914707477:ℚ)/163840000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((422940893:ℚ)/625000000),((6937358713:ℚ)/10000000000),((-5897358713:ℚ)/13112500000),((-800195417:ℚ)/2225000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2362845029:ℚ)/5000000000),((938341306361470316556447623466257129756323415249030703:ℚ)/18054503930664062500000000000000000000000000000000000000),((23858826011313261127533:ℚ)/160000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((6886102047:ℚ)/10000000000),((3498444829:ℚ)/5000000000),((-992814943:ℚ)/2225000000),((-39242714329:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2184519703:ℚ)/5000000000),((139312525037309173895310081989470561473962672998680190399:ℚ)/2718203048324584960937500000000000000000000000000000000000),((2188797527635068011409203533:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((3472810987:ℚ)/5000000000),((3528208933:ℚ)/5000000000),((-3008208933:ℚ)/6734375000),((-19829676909:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((418012333:ℚ)/1000000000),((22159805352070980296346494857689192347484730197213949814381:ℚ)/432469946713281250000000000000000000000000000000000000000000),((545180019361777025990542053:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7005139359:ℚ)/10000000000),((711594341:ℚ)/1000000000),((-607594341:ℚ)/1358750000),((-40075975513:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1991407321:ℚ)/5000000000),((4248396041118965877722219334917149308051633805435169195923:ℚ)/82930009280664062500000000000000000000000000000000000000000),((2172637561133902390397534797:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((1766163567:ℚ)/2500000000),((7175466357:ℚ)/10000000000),((-6135466357:ℚ)/13706250000),((-1446163567:ℚ)/3950000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1887896893:ℚ)/5000000000),((676002004858191162331156619338268728373606009433812449:ℚ)/13198663659667968750000000000000000000000000000000000000),((135284373151056374459150893:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((1424833353:ℚ)/2000000000),((7205226879:ℚ)/10000000000),((-880746697:ℚ)/1975000000),((-8181833471:ℚ)/22215000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((1778680641:ℚ)/5000000000),((7650742242720961992589162328206112085874327423145383639:ℚ)/150363892757226562500000000000000000000000000000000000000),((86258291890623417956482333:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((447120133:ℚ)/625000000),((904373347:ℚ)/1250000000),((-258124449:ℚ)/578515625),((-2569840931:ℚ)/6971875000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((215199381:ℚ)/625000000),((9974594264566456717842499147190294068218720398819367941:ℚ)/196048655880343914031982421875000000000000000000000000000),((8407847860926653748836293:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((448979807:ℚ)/625000000),((7294504729:ℚ)/10000000000),((-6254504729:ℚ)/13943750000),((-860952883:ℚ)/2343750000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((25978629:ℚ)/78125000),((11966961013172694882878027826589826462104968283312361:ℚ)/233750324696302413940429687500000000000000000000000000),((8392029429290508682232013:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7243184769:ℚ)/10000000000),((183850507:ℚ)/250000000),((-157850507:ℚ)/351562500),((-41742293383:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3076407533:ℚ)/10000000000),((10510332555108096980313602401734549440486383289711244593:ℚ)/205341171837890625000000000000000000000000000000000000000),((5928688844275689790447237:ℚ)/40960000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((3651345197:ℚ)/5000000000),((7413533489:ℚ)/10000000000),((-6373533489:ℚ)/14181250000),((-21079416379:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1403164959:ℚ)/5000000000),((135816649297973484571236287985976076438272330333605278659129:ℚ)/2654010273200000000000000000000000000000000000000000000000000),((1476557276066534576336653:ℚ)/10240000000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((3681096921:ℚ)/5000000000),((7532553109:ℚ)/10000000000),((-6492553109:ℚ)/14300000000),((-21287678447:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2508180207:ℚ)/10000000000),((9098813230943893698251640932126726842330587448659293393839:ℚ)/175737810797656250000000000000000000000000000000000000000000),((531008907143779817872093117:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7481194423:ℚ)/10000000000),((7651564033:ℚ)/10000000000),((-6611564033:ℚ)/14537500000),((-43408360961:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((354098423:ℚ)/2000000000),((5750571549499443972525543944067805066736618565398774501271:ℚ)/111144609987500000000000000000000000000000000000000000000000),((2107794109555256766696038173:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((7600186923:ℚ)/10000000000),((3944780711:ℚ)/5000000000),((-3424780711:ℚ)/7387500000),((-44241308461:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((354471394022142723052217240575947938231057012414535680302109:ℚ)/6707288550000000000000000000000000000000000000000000000000000),((144844711:ℚ)/1024000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((3919074599:ℚ)/5000000000),((8365468449:ℚ)/10000000000),((-7325468449:ℚ)/15250000000),((-22953522193:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((210715740434110773540278122988062604801957146383473495489:ℚ)/3842121600000000000000000000000000000000000000000000000000),((144844711:ℚ)/1024000000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8313992207:ℚ)/10000000000),((10268233079:ℚ)/10000000000),((-1025359231:ℚ)/1800000000),((-49237945449:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((14937442684802678335612769492294558971616326521973700927119:ℚ)/230400000000000000000000000000000000000000000000000000000000),((144844711:ℚ)/1024000000)⟩
theorem valid16 : Valid source15 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((2554140457:ℚ)/2500000000),((14071475631:ℚ)/10000000000),((-13031475631:ℚ)/20000000000),((-15638983199:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6567461684624881211417096634144090450371946364776711107:ℚ)/87602400000000000000000000000000000000000000000000000000),((144844711:ℚ)/1024000000)⟩
theorem valid17 : Valid source15 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((2231:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC09
#check @N11Formalization.C450Source15GroupedC09.bound
#print axioms N11Formalization.C450Source15GroupedC09.valid0
#print axioms N11Formalization.C450Source15GroupedC09.valid1
#print axioms N11Formalization.C450Source15GroupedC09.valid2
#print axioms N11Formalization.C450Source15GroupedC09.valid3
#print axioms N11Formalization.C450Source15GroupedC09.valid4
#print axioms N11Formalization.C450Source15GroupedC09.valid5
#print axioms N11Formalization.C450Source15GroupedC09.valid6
#print axioms N11Formalization.C450Source15GroupedC09.valid7
#print axioms N11Formalization.C450Source15GroupedC09.valid8
#print axioms N11Formalization.C450Source15GroupedC09.valid9
#print axioms N11Formalization.C450Source15GroupedC09.valid10
#print axioms N11Formalization.C450Source15GroupedC09.valid11
#print axioms N11Formalization.C450Source15GroupedC09.valid12
#print axioms N11Formalization.C450Source15GroupedC09.valid13
#print axioms N11Formalization.C450Source15GroupedC09.valid14
#print axioms N11Formalization.C450Source15GroupedC09.valid15
#print axioms N11Formalization.C450Source15GroupedC09.valid16
#print axioms N11Formalization.C450Source15GroupedC09.valid17
#print axioms N11Formalization.C450Source15GroupedC09.bound
#print axioms N11Formalization.C450Source15GroupedC09.endpoint_checks
