import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((3136126611:ℚ)/5000000000),((408806911:ℚ)/625000000),((-344806911:ℚ)/1240000000),((-2416126611:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((9376083:ℚ)/15625000),((10046254788709322729232907662182870995767998525444289631:ℚ)/413507531738281250000000000000000000000000000000000000000),((577157856253218197596971:ℚ)/11552000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((1627509841:ℚ)/2500000000),((423670901:ℚ)/625000000),((-359670901:ℚ)/1287500000),((-1267509841:ℚ)/6675000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1084366593:ℚ)/2000000000),((1155022215323094197956353997173812304475571914979478613:ℚ)/47864228247070312500000000000000000000000000000000000000),((563504735078780180550851:ℚ)/11552000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6747805109:ℚ)/10000000000),((1724409457:ℚ)/2500000000),((-489469819:ℚ)/1780000000),((-5307805109:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((59762937:ℚ)/125000000),((2967916777180187893766760127078896327947366581725427679:ℚ)/125426318652343750000000000000000000000000000000000000000),((8787139609356572951318299:ℚ)/184832000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((3433340501:ℚ)/5000000000),((175413399:ℚ)/250000000),((-149813399:ℚ)/543500000),((-2713340501:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2214523077:ℚ)/5000000000),((2837821782168108943180095188059334370543453994620071837:ℚ)/120212110551452636718750000000000000000000000000000000000),((86784125188809218102251:ℚ)/1848320000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1746388141:ℚ)/2500000000),((707598313:ℚ)/1000000000),((-605198313:ℚ)/2212000000),((-1386388141:ℚ)/6971875000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((126523429:ℚ)/312500000),((244680764594239062387001337103286387261299798568159881:ℚ)/10457693325150012969970703125000000000000000000000000000),((1370259847909017058965419:ℚ)/29573120000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((704498679:ℚ)/1000000000),((7135429079:ℚ)/10000000000),((-6111429079:ℚ)/22310000000),((-62277631:ℚ)/312500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3845377231:ℚ)/10000000000),((116562259105413121704420974368371977725926794868353:ℚ)/4986673593521118164062500000000000000000000000000000),((136158150319519002896469291:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-5:ℚ)/16),((-1:ℚ)/4),((3552210007:ℚ)/5000000000),((1433030321:ℚ)/2000000000),((-409410107:ℚ)/1500000000),((-2832210007:ℚ)/14121875000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1815615029:ℚ)/5000000000),((1229073018913647199943095906417890016565371543345953751:ℚ)/52805402961158752441406250000000000000000000000000000000),((5409782264812568127384091:ℚ)/118292480000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3567068129:ℚ)/5000000000),((3597436919:ℚ)/5000000000),((-3085436919:ℚ)/11297500000),((-2847068129:ℚ)/14181250000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3519503987:ℚ)/10000000000),((4685103199495477713311043643079855367920388310510629269:ℚ)/201375163961681365966796875000000000000000000000000000000),((33702783490578486643989611:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-5:ℚ)/16),((-1:ℚ)/4),((7163852261:ℚ)/10000000000),((361229789:ℚ)/500000000),((-310029789:ℚ)/1134500000),((-5723852261:ℚ)/28481250000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((340427123:ℚ)/1000000000),((362830127042323603321857463215950929405009358113599967511:ℚ)/15601715574458312988281250000000000000000000000000000000000),((335944768530182026599571:ℚ)/7393280000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((3596784013:ℚ)/5000000000),((1813579359:ℚ)/2500000000),((-222511337:ℚ)/813750000),((-2876784013:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3285162259:ℚ)/10000000000),((39511502436025560598142402576112513586510847631699101971:ℚ)/1699695318750000000000000000000000000000000000000000000000),((8371554807711721619423931:ℚ)/184832000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1805820889:ℚ)/2500000000),((3656879951:ℚ)/5000000000),((-3144879951:ℚ)/11440000000),((-1445820889:ℚ)/7209375000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3161738471:ℚ)/10000000000),((83174270512175016280919156919651633577801676040049:ℚ)/3567775408007204532623291015625000000000000000000000),((33389838897525679975591451:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((7282713923:ℚ)/10000000000),((460825079:ℚ)/625000000),((-396825079:ℚ)/1441875000),((-5842713923:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((579944349:ℚ)/2000000000),((8255122384088816897162584523894466623040240188177255472451:ℚ)/354394343977441406250000000000000000000000000000000000000000),((518338511383289462812291:ℚ)/11552000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((917767923:ℚ)/1250000000),((7432641549:ℚ)/10000000000),((-6408641549:ℚ)/23260000000),((-737767923:ℚ)/3664062500),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1306179819:ℚ)/5000000000),((1188904200045352266327982588877484217611011386621844737:ℚ)/51079932096600532531738281250000000000000000000000000000),((131830745740113433351798451:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7401571961:ℚ)/10000000000),((7492080783:ℚ)/10000000000),((-6468080783:ℚ)/23450000000),((-5961571961:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1145062513:ℚ)/5000000000),((20941925367359532932814616783222907342098196413077299779:ℚ)/900421859179687500000000000000000000000000000000000000000),((130967615713338148679248539:ℚ)/2957312000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((1865249919:ℚ)/2500000000),((77298277:ℚ)/100000000),((-22352759:ℚ)/78800000),((-1505249919:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1915491631:ℚ)/10000000000),((12917831490316267478499047228555523203650118812670451593:ℚ)/545840539550781250000000000000000000000000000000000000000),((10706033970606969:ℚ)/243200000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((1539740463:ℚ)/2000000000),((8205278033:ℚ)/10000000000),((-7181278033:ℚ)/24400000000),((-417246821:ℚ)/2160000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((30877437918134142385579258156660764753970487218220417:ℚ)/1280707200000000000000000000000000000000000000000000000),((44300653:ℚ)/1024000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((4087035951:ℚ)/5000000000),((2021330221:ℚ)/2000000000),((-1816530221:ℚ)/5184000000),((-3367035951:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((107578554484852282047790504576637678673292555951564772141:ℚ)/4050000000000000000000000000000000000000000000000000000000),((44300653:ℚ)/1024000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((2015039769:ℚ)/2000000000),((13908262259:ℚ)/10000000000),((-12884262259:ℚ)/32000000000),((-575679923:ℚ)/3680000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6971115495205882602539661998948258698034746220461691:ℚ)/233606400000000000000000000000000000000000000000000000),((44300653:ℚ)/1024000000)⟩
theorem valid17 : Valid tenth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((4557:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((4557:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((4557:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((469:ℚ)/640) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC12
#check @N11Formalization.C450TenthGroupedC12.bound
#print axioms N11Formalization.C450TenthGroupedC12.valid0
#print axioms N11Formalization.C450TenthGroupedC12.valid1
#print axioms N11Formalization.C450TenthGroupedC12.valid2
#print axioms N11Formalization.C450TenthGroupedC12.valid3
#print axioms N11Formalization.C450TenthGroupedC12.valid4
#print axioms N11Formalization.C450TenthGroupedC12.valid5
#print axioms N11Formalization.C450TenthGroupedC12.valid6
#print axioms N11Formalization.C450TenthGroupedC12.valid7
#print axioms N11Formalization.C450TenthGroupedC12.valid8
#print axioms N11Formalization.C450TenthGroupedC12.valid9
#print axioms N11Formalization.C450TenthGroupedC12.valid10
#print axioms N11Formalization.C450TenthGroupedC12.valid11
#print axioms N11Formalization.C450TenthGroupedC12.valid12
#print axioms N11Formalization.C450TenthGroupedC12.valid13
#print axioms N11Formalization.C450TenthGroupedC12.valid14
#print axioms N11Formalization.C450TenthGroupedC12.valid15
#print axioms N11Formalization.C450TenthGroupedC12.valid16
#print axioms N11Formalization.C450TenthGroupedC12.valid17
#print axioms N11Formalization.C450TenthGroupedC12.bound
#print axioms N11Formalization.C450TenthGroupedC12.endpoint_checks
