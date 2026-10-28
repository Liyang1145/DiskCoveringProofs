import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/2),((9:ℚ)/16),((5303489757:ℚ)/10000000000),((1412209813:ℚ)/2500000000),((8023489757:ℚ)/12875000000),((18309888317:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((998045353:ℚ)/1250000000),((-5447860975062122733113278786073607019721747440872203789473:ℚ)/14728670400000000000000000000000000000000000000000000000000),((-3243571360792845621442323:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((693134931:ℚ)/1250000000),((2945134131:ℚ)/5000000000),((1033134931:ℚ)/1668750000),((37706207179:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7530364797:ℚ)/10000000000),((-10517743587774245817122974386607498216134611643995426158457:ℚ)/28492002832031250000000000000000000000000000000000000000000),((-50101303991381862427627:ℚ)/112812500000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((2893185549:ℚ)/5000000000),((751359663:ℚ)/1250000000),((4253185549:ℚ)/6793750000),((9562236967:ℚ)/13350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1410761931:ℚ)/2000000000),((-1023473701637943474629577690233095673019190543040790152803:ℚ)/2694028018359375000000000000000000000000000000000000000000),((-1599631178413110576815171:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((5906915231:ℚ)/10000000000),((3065710509:ℚ)/5000000000),((8626915231:ℚ)/13825000000),((38791394581:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3402758557:ℚ)/5000000000),((-4931089233528082432245346497270430391590900510326787015079:ℚ)/13005141415264892578125000000000000000000000000000000000000),((-3179126845961657472439913:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((1205479273:ℚ)/2000000000),((1562975703:ℚ)/2500000000),((1749479273:ℚ)/2812500000),((19666781327:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6549498623:ℚ)/10000000000),((-878930377435629325921943207320059842387673800786812223:ℚ)/2322405079650878906250000000000000000000000000000000000),((-3158358698881481023090403:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((1229563557:ℚ)/2000000000),((631212149:ℚ)/1000000000),((1773563557:ℚ)/2836250000),((7920909341:ℚ)/11250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6284777581:ℚ)/10000000000),((-9667904555424082402287927801815336956721885176819953449:ℚ)/25239578247070312500000000000000000000000000000000000000),((-126154569272763244764423:ℚ)/288800000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((3104003533:ℚ)/5000000000),((318616293:ℚ)/500000000),((405818503:ℚ)/650000000),((3987546637:ℚ)/5672500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((307439689:ℚ)/500000000),((-2837305873380661972778791855915097460134450659848160121:ℚ)/7415097871923828125000000000000000000000000000000000000),((-62861672278378590841579:ℚ)/144400000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((1567045637:ℚ)/2500000000),((6432516287:ℚ)/10000000000),((2247045637:ℚ)/3604687500),((80292646583:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6010171509:ℚ)/10000000000),((-161167036990407215034114115667227786655914661607397591589:ℚ)/421634096812500000000000000000000000000000000000000000000),((-1566072540751579655155289:ℚ)/3610000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((6328344581:ℚ)/10000000000),((10144833:ℚ)/15625000),((9048344581:ℚ)/14537500000),((126303497:ℚ)/180234375),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((293435991:ℚ)/500000000),((-3611304402685530161393653627991073763758593949217139:ℚ)/9457145981794595718383789062500000000000000000000000),((-124841947253474693153987:ℚ)/288800000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((99820211:ℚ)/156250000),((1322601471:ℚ)/2000000000),((142320211:ℚ)/230859375),((16383413239:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2862112473:ℚ)/5000000000),((-2187856736571880835973696425743342731341372592778993151161:ℚ)/5810408177981250000000000000000000000000000000000000000000),((-61845251858808492143971:ℚ)/144400000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((6508753317:ℚ)/10000000000),((6733271147:ℚ)/10000000000),((9228753317:ℚ)/15012500000),((82999440323:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5425111419:ℚ)/10000000000),((-1747692435699640885901535235289184851475330698498968776541129:ℚ)/4648434567581250000000000000000000000000000000000000000000000),((-3068967915894168243904833:ℚ)/7220000000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((6628964473:ℚ)/10000000000),((6853486911:ℚ)/10000000000),((9348964473:ℚ)/15250000000),((84081382199:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5110485139:ℚ)/10000000000),((-371943320410760425391790976309690380778484453598683014447633:ℚ)/990672559321875000000000000000000000000000000000000000000000),((-3045042480491038020797277:ℚ)/7220000000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((67491293:ℚ)/100000000),((7093783267:ℚ)/10000000000),((94691293:ℚ)/157250000),((86244049403:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((955449327:ℚ)/2000000000),((-979665986511661345028273864429504407920000695568155525485949:ℚ)/2676957168750000000000000000000000000000000000000000000000000),((-1491538121107721570577809:ℚ)/3610000000000000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((6989328561:ℚ)/10000000000),((916739113:ℚ)/1250000000),((9709328561:ℚ)/16200000000),((11050652017:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2018058917:ℚ)/5000000000),((-9724731261785431298340292484848839821162722943410481021:ℚ)/26601448095703125000000000000000000000000000000000000000),((-154253845136213891812293:ℚ)/380000000000000000000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((3614683491:ℚ)/5000000000),((9250397779:ℚ)/10000000000),((4974683491:ℚ)/10000000000),((105653580011:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3135892781:ℚ)/10000000000),((-5163084013288470446630189648446455218958074130867195919297:ℚ)/20407334400000000000000000000000000000000000000000000000000),((-193164176508099903:ℚ)/486400000000000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((1143160237:ℚ)/1250000000),((13069647271:ℚ)/10000000000),((1483160237:ℚ)/3450000000),((140026825439:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-6128351905310945628838313420629768625617:ℚ)/35328000000000000000000000000000000000000),((-10300273:ℚ)/25600000)⟩
theorem valid15 : Valid source36 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source36 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC25
#check @N11Formalization.C450Source36GroupedC25.bound
#print axioms N11Formalization.C450Source36GroupedC25.valid0
#print axioms N11Formalization.C450Source36GroupedC25.valid1
#print axioms N11Formalization.C450Source36GroupedC25.valid2
#print axioms N11Formalization.C450Source36GroupedC25.valid3
#print axioms N11Formalization.C450Source36GroupedC25.valid4
#print axioms N11Formalization.C450Source36GroupedC25.valid5
#print axioms N11Formalization.C450Source36GroupedC25.valid6
#print axioms N11Formalization.C450Source36GroupedC25.valid7
#print axioms N11Formalization.C450Source36GroupedC25.valid8
#print axioms N11Formalization.C450Source36GroupedC25.valid9
#print axioms N11Formalization.C450Source36GroupedC25.valid10
#print axioms N11Formalization.C450Source36GroupedC25.valid11
#print axioms N11Formalization.C450Source36GroupedC25.valid12
#print axioms N11Formalization.C450Source36GroupedC25.valid13
#print axioms N11Formalization.C450Source36GroupedC25.valid14
#print axioms N11Formalization.C450Source36GroupedC25.valid15
#print axioms N11Formalization.C450Source36GroupedC25.bound
#print axioms N11Formalization.C450Source36GroupedC25.endpoint_checks
