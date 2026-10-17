import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((2788689041:ℚ)/5000000000),((6129644863:ℚ)/10000000000),((12251859817:ℚ)/17800000000),((21588934589:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((11668769:ℚ)/15625000),((-99206943539841408178977570600167211:ℚ)/1409938000000000000000000000000000000),((-5515574914173687490801988943:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((151349829:ℚ)/250000000),((6367932681:ℚ)/10000000000),((281264017:ℚ)/395000000),((22303798043:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1622957181:ℚ)/2500000000),((-32744060523801731110847663531564058389360629713393:ℚ)/385186718750000000000000000000000000000000000000000),((-16442157557502226931293131901:ℚ)/44359680000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((251688683:ℚ)/400000000),((3303083959:ℚ)/5000000000),((3254975513:ℚ)/4576000000),((11509251877:ℚ)/13825000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((297700829:ℚ)/500000000),((-51097711706495599928342981308457229001966107796350673:ℚ)/598877593600000000000000000000000000000000000000000000),((-1361291651364189638693566207:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3265196347:ℚ)/5000000000),((6725267439:ℚ)/10000000000),((41997159817:ℚ)/58150000000),((23375802317:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((335606711:ℚ)/625000000),((-28180562758476975791721107726251667511607448481492079913:ℚ)/307233934960937500000000000000000000000000000000000000000),((-16281386684755628959985173261:ℚ)/44359680000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6649463879:ℚ)/10000000000),((273774227:ℚ)/400000000),((85304102669:ℚ)/118200000000),((949322681:ℚ)/1163000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1263765507:ℚ)/2500000000),((-236569861992347573924881576119775465590404223140062693621:ℚ)/2580313387500000000000000000000000000000000000000000000000),((-8654266969008027808722663:ℚ)/23658496000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6768524697:ℚ)/10000000000),((1392686633:ℚ)/2000000000),((86613771667:ℚ)/120100000000),((4818059899:ℚ)/5910000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1180359433:ℚ)/2500000000),((-992101259877318703603954084258933682847954436077166423683:ℚ)/10827022506250000000000000000000000000000000000000000000000),((-215621218160401077371045183:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((1721893911:ℚ)/2500000000),((7082500413:ℚ)/10000000000),((21980833021:ℚ)/30500000000),((24447501239:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4364454841:ℚ)/10000000000),((-16238345395476981518454135812245402205251845351025235581:ℚ)/177328906250000000000000000000000000000000000000000000000),((-16115908976304648985547180629:ℚ)/44359680000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((7006617183:ℚ)/10000000000),((3600778947:ℚ)/5000000000),((89232789013:ℚ)/123900000000),((12402336841:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1988898953:ℚ)/5000000000),((-90645680306274130174214673397590861956237034057574380559:ℚ)/990632770312500000000000000000000000000000000000000000000),((-4014925830161796770000976469:ℚ)/11089920000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1781412437:ℚ)/2500000000),((1830151513:ℚ)/2500000000),((22635536807:ℚ)/31450000000),((6290454539:ℚ)/7743750000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1775877201:ℚ)/5000000000),((-17358293553189971290285828948146984769030638091765127:ℚ)/189863730621337890625000000000000000000000000000000000),((-333395298174953106126187743:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((1811168437:ℚ)/2500000000),((3779338023:ℚ)/5000000000),((7654284269:ℚ)/10800000000),((12938014069:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1534965473:ℚ)/5000000000),((-25041876401927669367811511807001358838349437575576423:ℚ)/291600000000000000000000000000000000000000000000000000),((-3971986482742703483658008989:ℚ)/11089920000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7482697567:ℚ)/10000000000),((94622587:ℚ)/100000000),((94469673237:ℚ)/160000000000),((315867761:ℚ)/324000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1759227049:ℚ)/10000000000),((-51102916735823343994382780704718963018777355373763984277:ℚ)/1600000000000000000000000000000000000000000000000000000000),((-73258377:ℚ)/204800000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((1173248773:ℚ)/1250000000),((13266459581:ℚ)/10000000000),((14425736503:ℚ)/27600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((698628302331256301888815046044753:ℚ)/194672000000000000000000000000000000),((-73258377:ℚ)/204800000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC28
#check @N11Formalization.C450Source21GroupedC28.bound
#print axioms N11Formalization.C450Source21GroupedC28.valid0
#print axioms N11Formalization.C450Source21GroupedC28.valid1
#print axioms N11Formalization.C450Source21GroupedC28.valid2
#print axioms N11Formalization.C450Source21GroupedC28.valid3
#print axioms N11Formalization.C450Source21GroupedC28.valid4
#print axioms N11Formalization.C450Source21GroupedC28.valid5
#print axioms N11Formalization.C450Source21GroupedC28.valid6
#print axioms N11Formalization.C450Source21GroupedC28.valid7
#print axioms N11Formalization.C450Source21GroupedC28.valid8
#print axioms N11Formalization.C450Source21GroupedC28.valid9
#print axioms N11Formalization.C450Source21GroupedC28.valid10
#print axioms N11Formalization.C450Source21GroupedC28.valid11
#print axioms N11Formalization.C450Source21GroupedC28.bound
#print axioms N11Formalization.C450Source21GroupedC28.endpoint_checks
