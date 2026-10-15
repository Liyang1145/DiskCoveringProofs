import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((9:ℚ)/16),((5:ℚ)/8),((2689412667:ℚ)/5000000000),((2856577459:ℚ)/5000000000),((33484714003:ℚ)/51500000000),((3816577459:ℚ)/4960000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7845020071:ℚ)/10000000000),((-2540587915771325981009860568330659073579508069418706569097:ℚ)/8090949606400000000000000000000000000000000000000000000000),((-1618353769505807818826828979:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((2809489999:ℚ)/5000000000),((372077407:ℚ)/625000000),((34565409991:ℚ)/53400000000),((492077407:ℚ)/643750000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1477414957:ℚ)/2000000000),((-3098702722701864137620873287384733998907167868598222183:ℚ)/9905422859573364257812500000000000000000000000000000000),((-24983535514233577537514491:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((5858942803:ℚ)/10000000000),((759151439:ℚ)/1250000000),((71290485227:ℚ)/108700000000),((999151439:ℚ)/1335000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3452610871:ℚ)/5000000000),((-208178286609724683955291140761312466642070053750491844791:ℚ)/650757434657031250000000000000000000000000000000000000000),((-99565700317596587866829339:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((373678667:ℚ)/625000000),((774142733:ℚ)/1250000000),((4523108003:ℚ)/6912500000),((1014142733:ℚ)/1358750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((831705391:ℚ)/1250000000),((-23908776828312973590441351374997106438471481114507950199:ℚ)/74915033360848808288574218750000000000000000000000000000),((-98914901308020701025299251:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((6098733913:ℚ)/10000000000),((6313031771:ℚ)/10000000000),((73448605217:ℚ)/112500000000),((8233031771:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6393814689:ℚ)/10000000000),((-40566693324762902040839340283829829027958208092202237:ℚ)/127400507226562500000000000000000000000000000000000000),((-6287771685821236998904922819:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6218570623:ℚ)/10000000000),((1608220821:ℚ)/2500000000),((74527135607:ℚ)/114400000000),((696073607:ℚ)/937500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((6124657553:ℚ)/10000000000),((-309804969198005373210411005623763037744942676483340323:ℚ)/975084304809570312500000000000000000000000000000000000),((-390241201900597012195541219:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1267674151:ℚ)/2000000000),((6552698321:ℚ)/10000000000),((15121067359:ℚ)/23260000000),((8472698321:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((730606717:ℚ)/1250000000),((-364801075363286325562644438024548703467194263423620911791737:ℚ)/1150601232809600000000000000000000000000000000000000000000000),((-326253510086643836573659801:ℚ)/778240000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3229068067:ℚ)/5000000000),((6672478671:ℚ)/10000000000),((38341612603:ℚ)/59100000000),((8592478671:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((138819103:ℚ)/250000000),((-90545327204350725311420808945843009691108376743046451407359:ℚ)/286162602765576562500000000000000000000000000000000000000000),((-6152644420645117316670021019:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6577868463:ℚ)/10000000000),((6792226009:ℚ)/10000000000),((77760816167:ℚ)/120100000000),((8712226009:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5246306449:ℚ)/10000000000),((-43531743050998263956558463306829907819561680185253204222089:ℚ)/137846170757162500000000000000000000000000000000000000000000),((-6105342744404339243897061579:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((6697569337:ℚ)/10000000000),((3455970951:ℚ)/5000000000),((78838124033:ℚ)/122000000000),((4415970951:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((984553297:ℚ)/2000000000),((-1587391211817241743767082156808183706831755343148787590557:ℚ)/5035918843219531250000000000000000000000000000000000000000),((-1514227992490582635022520459:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6817240247:ℚ)/10000000000),((3575642571:ℚ)/5000000000),((79915162223:ℚ)/125800000000),((4535642571:ℚ)/6100000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((4578491373:ℚ)/10000000000),((-43215558608599212009352906777890686180081282013712857758033:ℚ)/140317171595312500000000000000000000000000000000000000000000),((-1484943935638413977061325219:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((1764124423:ℚ)/2500000000),((7390519103:ℚ)/10000000000),((20517119807:ℚ)/32400000000),((9310519103:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((951199653:ℚ)/2500000000),((-225967984151991960476942443845575971892763674721702344419:ℚ)/735476836950000000000000000000000000000000000000000000000),((-5835022375070664653876859131:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7295650997:ℚ)/10000000000),((4650700781:ℚ)/5000000000),((84220858973:ℚ)/160000000000),((5610700781:ℚ)/6480000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((567916137:ℚ)/2000000000),((-14315538475194738932905922270060553913863248167612181:ℚ)/62985600000000000000000000000000000000000000000000000),((-94469402931167951:ℚ)/243200000000000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((4603014161:ℚ)/5000000000),((13114131989:ℚ)/10000000000),((50707127449:ℚ)/110400000000),((15034131989:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-270229804423001065292510395903606914703:ℚ)/1625088000000000000000000000000000000000),((-400741073:ℚ)/1024000000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC26
#check @N11Formalization.C450Source31GroupedC26.bound
#print axioms N11Formalization.C450Source31GroupedC26.valid0
#print axioms N11Formalization.C450Source31GroupedC26.valid1
#print axioms N11Formalization.C450Source31GroupedC26.valid2
#print axioms N11Formalization.C450Source31GroupedC26.valid3
#print axioms N11Formalization.C450Source31GroupedC26.valid4
#print axioms N11Formalization.C450Source31GroupedC26.valid5
#print axioms N11Formalization.C450Source31GroupedC26.valid6
#print axioms N11Formalization.C450Source31GroupedC26.valid7
#print axioms N11Formalization.C450Source31GroupedC26.valid8
#print axioms N11Formalization.C450Source31GroupedC26.valid9
#print axioms N11Formalization.C450Source31GroupedC26.valid10
#print axioms N11Formalization.C450Source31GroupedC26.valid11
#print axioms N11Formalization.C450Source31GroupedC26.valid12
#print axioms N11Formalization.C450Source31GroupedC26.valid13
#print axioms N11Formalization.C450Source31GroupedC26.bound
#print axioms N11Formalization.C450Source31GroupedC26.endpoint_checks
