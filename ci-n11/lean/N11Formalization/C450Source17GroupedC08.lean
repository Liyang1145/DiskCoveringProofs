import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((3239093717:ℚ)/5000000000),((6775715571:ℚ)/10000000000),((-51381440139:ℚ)/99200000000),((-2599093717:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2751257079:ℚ)/5000000000),((4976662396514276014517103928940533160211935083734659497:ℚ)/77532662200927734375000000000000000000000000000000000000),((790022814438474952711926861:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1343298971:ℚ)/2000000000),((1723715361:ℚ)/2500000000),((-13113438249:ℚ)/25750000000),((-1087298971:ℚ)/2622500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2434908549:ℚ)/5000000000),((90058112064655152143276956090874067770929363211653821:ℚ)/1451355308190917968750000000000000000000000000000000000),((124974758149191375548729709:ℚ)/591462400000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((3417813261:ℚ)/5000000000),((1402798633:ℚ)/2000000000),((-10705187697:ℚ)/20980000000),((-2777813261:ℚ)/6675000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4523452083:ℚ)/10000000000),((15123396508869463847087831316841478297610992821169046637:ℚ)/243735803063964843750000000000000000000000000000000000000),((776604213043493862608418429:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((3477372273:ℚ)/5000000000),((7073553953:ℚ)/10000000000),((-18020661859:ℚ)/35600000000),((-2837372273:ℚ)/6734375000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4150455197:ℚ)/10000000000),((60790444984480569219735844542518764714678798648774147:ℚ)/995435686642304062843322753906250000000000000000000000),((772100997282665180048198421:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1753574667:ℚ)/2500000000),((3566555739:ℚ)/5000000000),((-27299001651:ℚ)/53875000000),((-1433574667:ℚ)/3396875000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((987906157:ℚ)/2500000000),((3224476254120446104351738824920950630758352285011257669:ℚ)/52791741542148590087890625000000000000000000000000000000),((192460921530148465336082061:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((3536924823:ℚ)/5000000000),((7192665827:ℚ)/10000000000),((-55133992443:ℚ)/108700000000),((-2896924823:ℚ)/6853125000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3742838477:ℚ)/10000000000),((5565734705762932639290500899698948698686052581343798459:ℚ)/91109629336667060852050781250000000000000000000000000000),((767582569221953379853743621:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-9:ℚ)/16),((-1:ℚ)/2),((7133397561:ℚ)/10000000000),((1444488367:ℚ)/2000000000),((-217262653:ℚ)/430000000),((-5853397561:ℚ)/13765625000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3522322421:ℚ)/10000000000),((5312416056716697068565434116833314424347609865713763051:ℚ)/87628683933615684509277343750000000000000000000000000000),((3061270576499372675462753829:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((1432634079:ℚ)/2000000000),((181305427:ℚ)/250000000),((-1391748843:ℚ)/2753125000),((-1176634079:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3406957303:ℚ)/10000000000),((165404976463414846615897339863966473528458886950680349:ℚ)/2728051833563232421875000000000000000000000000000000000),((122269400437410338360280309:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7192942493:ℚ)/10000000000),((7311765319:ℚ)/10000000000),((-8029412553:ℚ)/15800000000),((-5912942493:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((82192809:ℚ)/250000000),((26350866146476568662824713964747236418216520686022643:ℚ)/431245085573196411132812500000000000000000000000000000),((3052195633536450039296735901:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((7252484519:ℚ)/10000000000),((7371310619:ℚ)/10000000000),((-56741795571:ℚ)/111550000000),((-663609391:ℚ)/1562500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3035737389:ℚ)/10000000000),((19046249478033113860711743683857835246431995250139339:ℚ)/311667099595069885253906250000000000000000000000000000),((3043105438592371593475833189:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7312023711:ℚ)/10000000000),((1486170611:ℚ)/2000000000),((-3818511833:ℚ)/7500000000),((-6032023711:ℚ)/14181250000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((690410753:ℚ)/2500000000),((1361740571470931449788260503600911991748384605857967:ℚ)/22280943124771118164062500000000000000000000000000000),((3033999982944484053882631029:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7371560143:ℚ)/10000000000),((7490392699:ℚ)/10000000000),((-57813534291:ℚ)/113450000000),((-6091560143:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((491606949:ℚ)/2000000000),((1267331957784259141138589028069990324248100947027739747859:ℚ)/20734455259375000000000000000000000000000000000000000000000),((3024879257487461317018980501:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7431093883:ℚ)/10000000000),((1902365971:ℚ)/2500000000),((-14721293739:ℚ)/28600000000),((-6151093883:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((528054233:ℚ)/2500000000),((6548288409615779332962181784843053425216462226927923969:ℚ)/105611665142822265625000000000000000000000000000000000000),((3015743253959406136886265261:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((471884597:ℚ)/625000000),((3864262351:ℚ)/5000000000),((-29978361159:ℚ)/58150000000),((-130628199:ℚ)/307812500),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1145942867:ℚ)/10000000000),((1642635611887598272420009783257737307819198219255081:ℚ)/26498939988017082214355468750000000000000000000000000),((11708692892041119849446541:ℚ)/57760000000000000000000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((1917300807:ℚ)/2500000000),((1991654297:ℚ)/2500000000),((-5174962891:ℚ)/9850000000),((-1597300807:ℚ)/3812500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((6510402446133916221216046065318702712799992833248240609:ℚ)/102345101165771484375000000000000000000000000000000000000),((207045543:ℚ)/1024000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((7907274477:ℚ)/10000000000),((2110674393:ℚ)/2500000000),((-16596069537:ℚ)/30500000000),((-6627274477:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((17972398887811966956346932755130803160956066124536122723:ℚ)/270149175000000000000000000000000000000000000000000000000),((207045543:ℚ)/1024000000)⟩
theorem valid15 : Valid source17 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((8383316149:ℚ)/10000000000),((10345990189:ℚ)/10000000000),((-27837970567:ℚ)/43200000000),((-7103316149:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((61426797106263924888707984996510753676015355291217465317:ℚ)/755827200000000000000000000000000000000000000000000000000),((207045543:ℚ)/1024000000)⟩
theorem valid16 : Valid source17 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((10286490873:ℚ)/10000000000),((14149851343:ℚ)/10000000000),((-117748662087:ℚ)/160000000000),((-9006490873:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1499480682596352124866666754489965348086787587802085158466919:ℚ)/15235200000000000000000000000000000000000000000000000000000000),((207045543:ℚ)/1024000000)⟩
theorem valid17 : Valid source17 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((2231:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC08
#check @N11Formalization.C450Source17GroupedC08.bound
#print axioms N11Formalization.C450Source17GroupedC08.valid0
#print axioms N11Formalization.C450Source17GroupedC08.valid1
#print axioms N11Formalization.C450Source17GroupedC08.valid2
#print axioms N11Formalization.C450Source17GroupedC08.valid3
#print axioms N11Formalization.C450Source17GroupedC08.valid4
#print axioms N11Formalization.C450Source17GroupedC08.valid5
#print axioms N11Formalization.C450Source17GroupedC08.valid6
#print axioms N11Formalization.C450Source17GroupedC08.valid7
#print axioms N11Formalization.C450Source17GroupedC08.valid8
#print axioms N11Formalization.C450Source17GroupedC08.valid9
#print axioms N11Formalization.C450Source17GroupedC08.valid10
#print axioms N11Formalization.C450Source17GroupedC08.valid11
#print axioms N11Formalization.C450Source17GroupedC08.valid12
#print axioms N11Formalization.C450Source17GroupedC08.valid13
#print axioms N11Formalization.C450Source17GroupedC08.valid14
#print axioms N11Formalization.C450Source17GroupedC08.valid15
#print axioms N11Formalization.C450Source17GroupedC08.valid16
#print axioms N11Formalization.C450Source17GroupedC08.valid17
#print axioms N11Formalization.C450Source17GroupedC08.bound
#print axioms N11Formalization.C450Source17GroupedC08.endpoint_checks
