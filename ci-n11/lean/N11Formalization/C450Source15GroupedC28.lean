import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5768925591:ℚ)/10000000000),((6306810263:ℚ)/10000000000),((71778181501:ℚ)/106800000000),((21160430789:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7089142513:ℚ)/10000000000),((-3336569118066780054459652889639770579:ℚ)/101515536000000000000000000000000000000),((-4016743970536506886781805393:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((156117873:ℚ)/250000000),((6544678101:ℚ)/10000000000),((1925296603:ℚ)/2765000000),((21874034303:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6064561629:ℚ)/10000000000),((-5190496380475281077355200683048930015561854171025637:ℚ)/132119044531250000000000000000000000000000000000000000),((-4007480277882542825913925497:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6482568813:ℚ)/10000000000),((6782521449:ℚ)/10000000000),((79628256943:ℚ)/114400000000),((22587564347:ℚ)/27650000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((171608727:ℚ)/312500000),((-369954441093714583135501607811905539839901124440711939873:ℚ)/9357462400000000000000000000000000000000000000000000000000),((-3998150115693700204548585297:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3360199573:ℚ)/5000000000),((6901434691:ℚ)/10000000000),((41122195303:ℚ)/58150000000),((22944304073:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((303676737:ℚ)/625000000),((-13011484816133963078196221825568818340352174978878098817:ℚ)/307233934960937500000000000000000000000000000000000000000),((-3993460085329048001185075657:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6839306201:ℚ)/10000000000),((280813707:ℚ)/400000000),((83552368211:ℚ)/118200000000),((932041121:ℚ)/1163000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4512361989:ℚ)/10000000000),((-36456359978989966687778422177374580131591254174707541023:ℚ)/860104462500000000000000000000000000000000000000000000000),((-6382005457435015088935353:ℚ)/23658496000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((3479104099:ℚ)/5000000000),((3539897387:ℚ)/5000000000),((42430145089:ℚ)/59575000000),((11739692161:ℚ)/14775000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4139138381:ℚ)/10000000000),((-57768987098249146205356977030432380175109265964384587759:ℚ)/1321515223339843750000000000000000000000000000000000000000),((-996598457431444034524169593:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((56141259:ℚ)/80000000),((7139245651:ℚ)/10000000000),((684113849:ℚ)/960800000),((23657736953:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((39401287:ℚ)/100000000),((-15145174706956760239013050304782336812529976081719:ℚ)/346464720200000000000000000000000000000000000000000),((-3984030084683860913648742697:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((221159543:ℚ)/312500000),((3599347667:ℚ)/5000000000),((299194997:ℚ)/420312500),((11918043001:ℚ)/15012500000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((932775953:ℚ)/2500000000),((-20285858406757328110689894345472830852421046343343:ℚ)/464084362983703613281250000000000000000000000000000),((-995415543728660913657416233:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((713655223:ℚ)/1000000000),((1814535963:ℚ)/2500000000),((8682207453:ℚ)/12200000000),((6003607889:ℚ)/7565625000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((351027091:ℚ)/1000000000),((-496050511208770714614052753664847726736752831382904907:ℚ)/11349050000000000000000000000000000000000000000000000000),((-248705631219609489900800793:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3597998981:ℚ)/5000000000),((7377037501:ℚ)/10000000000),((2082761371:ℚ)/2950000000),((24371112503:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3275238021:ℚ)/10000000000),((-1703027925665069734543448981152428177965698512101221:ℚ)/40113085937500000000000000000000000000000000000000000),((-3974533448478964224850929097:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((7314886167:ℚ)/10000000000),((3747963401:ℚ)/5000000000),((88783747837:ℚ)/125800000000),((1766270029:ℚ)/2212500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((171737253:ℚ)/625000000),((-516035635776064701661636992659551661374982259786967107:ℚ)/12151278759765625000000000000000000000000000000000000000),((-992440031327404175708823697:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((7433770191:ℚ)/10000000000),((7733693131:ℚ)/10000000000),((90091472101:ℚ)/129600000000),((25441079393:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2095354143:ℚ)/10000000000),((-6743815879096934673873568010615044508888982744813227779:ℚ)/167961600000000000000000000000000000000000000000000000000),((-274623811:ℚ)/1024000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((767152643:ℚ)/1000000000),((2408841943:ℚ)/2500000000),((9270679073:ℚ)/16000000000),((7786525829:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-27244897290553351927912951065293669102315419587674863:ℚ)/1600000000000000000000000000000000000000000000000000000),((-274623811:ℚ)/1024000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((9573137643:ℚ)/10000000000),((2687466519:ℚ)/2000000000),((113624514073:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1817585091038506475126199700081939343:ℚ)/897048576000000000000000000000000000000),((-274623811:ℚ)/1024000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
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
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC28
#check @N11Formalization.C450Source15GroupedC28.bound
#print axioms N11Formalization.C450Source15GroupedC28.valid0
#print axioms N11Formalization.C450Source15GroupedC28.valid1
#print axioms N11Formalization.C450Source15GroupedC28.valid2
#print axioms N11Formalization.C450Source15GroupedC28.valid3
#print axioms N11Formalization.C450Source15GroupedC28.valid4
#print axioms N11Formalization.C450Source15GroupedC28.valid5
#print axioms N11Formalization.C450Source15GroupedC28.valid6
#print axioms N11Formalization.C450Source15GroupedC28.valid7
#print axioms N11Formalization.C450Source15GroupedC28.valid8
#print axioms N11Formalization.C450Source15GroupedC28.valid9
#print axioms N11Formalization.C450Source15GroupedC28.valid10
#print axioms N11Formalization.C450Source15GroupedC28.valid11
#print axioms N11Formalization.C450Source15GroupedC28.valid12
#print axioms N11Formalization.C450Source15GroupedC28.valid13
#print axioms N11Formalization.C450Source15GroupedC28.bound
#print axioms N11Formalization.C450Source15GroupedC28.endpoint_checks
