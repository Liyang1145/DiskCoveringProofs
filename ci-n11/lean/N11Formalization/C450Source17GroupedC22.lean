import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((1186309523:ℚ)/2000000000),((100986291:ℚ)/156250000),((1570309523:ℚ)/4272000000),((382958873:ℚ)/775000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6753842267:ℚ)/10000000000),((464960062578775781584802546555907617:ℚ)/16591957804687500000000000000000000000),((-435607329746564615544183:ℚ)/1805000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6408580673:ℚ)/10000000000),((837682887:ℚ)/1250000000),((1189797239:ℚ)/3160000000),((3153048661:ℚ)/6675000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5675244151:ℚ)/10000000000),((418183333418369957306932275243616018725920169721615801649:ℚ)/17401202824658203125000000000000000000000000000000000000000),((-377743474579485485132517:ℚ)/1520000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((1661747953:ℚ)/2500000000),((1705152983:ℚ)/2500000000),((2141747953:ℚ)/5625000000),((6395458949:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2530887489:ℚ)/5000000000),((2131180384324577370646559077038541145982641338040545429:ℚ)/95550380419921875000000000000000000000000000000000000000),((-29122441476088474668147663:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((1691543543:ℚ)/2500000000),((1387949491:ℚ)/2000000000),((167041811:ℚ)/440000000),((5187848473:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((945646721:ℚ)/2000000000),((1080029938134977532130847544493182341331602428136722349:ℚ)/48944091796875000000000000000000000000000000000000000000),((-18762149389275008329955127:ℚ)/73932800000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((1377068419:ℚ)/2000000000),((3529435161:ℚ)/5000000000),((1761068419:ℚ)/4652000000),((13148305483:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1092850491:ℚ)/2500000000),((1620763416373694901131170717901170042575285797511416152660487:ℚ)/74159845083431250000000000000000000000000000000000000000000000),((-118035166771925586835111407:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1751124073:ℚ)/2500000000),((1794495287:ℚ)/2500000000),((2231124073:ℚ)/5910000000),((6663485861:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((199249789:ℚ)/500000000),((6055267496829655273339534158783441061180757492402046825529:ℚ)/279455666763258361816406250000000000000000000000000000000000),((-29701242608628484301947023:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((7123637431:ℚ)/10000000000),((3648540253:ℚ)/5000000000),((9043637431:ℚ)/24020000000),((13505620759:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1779680273:ℚ)/5000000000),((7503443324311346149720845806052524984008302814697497205118731:ℚ)/348923119729067578125000000000000000000000000000000000000000000),((-119572849618245895377834903:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((1448553227:ℚ)/2000000000),((927021117:ℚ)/1250000000),((1832553227:ℚ)/4880000000),((3421063351:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1539113041:ℚ)/5000000000),((52531195405671518602966602486004468387621318277490965569:ℚ)/2458944747665786743164062500000000000000000000000000000000),((-7521175558418101652147463:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1840470747:ℚ)/2500000000),((7654315003:ℚ)/10000000000),((2320470747:ℚ)/6290000000),((28082945009:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((62745691:ℚ)/250000000),((1559837614950797252583295469571317119906309631045458243776607:ℚ)/70158585797656250000000000000000000000000000000000000000000000),((-3185245714618809:ℚ)/12160000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((950010413:ℚ)/1250000000),((7892423037:ℚ)/10000000000),((1190010413:ℚ)/3240000000),((28797269111:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((112335850604089567494861342749706955730197591339094956315097:ℚ)/5102370556340625000000000000000000000000000000000000000000000),((-34015881:ℚ)/128000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((7838242381:ℚ)/10000000000),((9796244603:ℚ)/10000000000),((9758242381:ℚ)/32000000000),((34508733809:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((30404839535112168680957999720910619:ℚ)/960000000000000000000000000000000000),((-34015881:ℚ)/128000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((4871192241:ℚ)/5000000000),((6800362639:ℚ)/5000000000),((1943730747:ℚ)/7360000000),((22961087917:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((300826660076104337250547:ℚ)/6771200000000000000000000),((-34015881:ℚ)/128000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC22
#check @N11Formalization.C450Source17GroupedC22.bound
#print axioms N11Formalization.C450Source17GroupedC22.valid0
#print axioms N11Formalization.C450Source17GroupedC22.valid1
#print axioms N11Formalization.C450Source17GroupedC22.valid2
#print axioms N11Formalization.C450Source17GroupedC22.valid3
#print axioms N11Formalization.C450Source17GroupedC22.valid4
#print axioms N11Formalization.C450Source17GroupedC22.valid5
#print axioms N11Formalization.C450Source17GroupedC22.valid6
#print axioms N11Formalization.C450Source17GroupedC22.valid7
#print axioms N11Formalization.C450Source17GroupedC22.valid8
#print axioms N11Formalization.C450Source17GroupedC22.valid9
#print axioms N11Formalization.C450Source17GroupedC22.valid10
#print axioms N11Formalization.C450Source17GroupedC22.valid11
#print axioms N11Formalization.C450Source17GroupedC22.bound
#print axioms N11Formalization.C450Source17GroupedC22.endpoint_checks
