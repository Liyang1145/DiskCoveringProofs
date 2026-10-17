import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((134474533:ℚ)/250000000),((5940257323:ℚ)/10000000000),((2100168929:ℚ)/2670000000),((48941801261:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7844729547:ℚ)/10000000000),((-633519807697858456111611946248448849:ℚ)/2379270375000000000000000000000000000),((-197694833187272811229874047:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((585512387:ℚ)/1000000000),((386152347:ℚ)/625000000),((9019661031:ℚ)/11060000000),((3163066429:ℚ)/3337500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6913107127:ℚ)/10000000000),((-179872737949823528299451788693391034089834076429269613:ℚ)/603972775000000000000000000000000000000000000000000000),((-2265963381152430449474461:ℚ)/6931200000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((1523284017:ℚ)/2500000000),((6297510363:ℚ)/10000000000),((23322692221:ℚ)/28125000000),((51442572541:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6406148347:ℚ)/10000000000),((-7247880784742425202844784417398630628539301339275107603:ℚ)/23174285888671875000000000000000000000000000000000000000),((-573561553688625090751215901:ℚ)/1774387200000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6212129151:ℚ)/10000000000),((641657241:ℚ)/1000000000),((94837678963:ℚ)/114400000000),((5227600687:ℚ)/5625000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((6139385237:ℚ)/10000000000),((-132856721901862533744545506129824715873345024640445085973:ℚ)/425339200000000000000000000000000000000000000000000000000),((-5670190230734396011865749:ℚ)/17743872000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((791389267:ℚ)/1250000000),((6476099563:ℚ)/10000000000),((4016020157:ℚ)/4806250000),((52692696941:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((5724742:ℚ)/9765625),((-83134778018537574675223165042402390334397452658263939:ℚ)/260213818931579589843750000000000000000000000000000000),((-187913734375089421305357567:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6390603717:ℚ)/10000000000),((6535624221:ℚ)/10000000000),((97157848321:ℚ)/116300000000),((53109369547:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((5719096913:ℚ)/10000000000),((-62768021534693228009654516028595228814480657812323295581:ℚ)/196629718375000000000000000000000000000000000000000000000),((-560459009490418454092867789:ℚ)/1774387200000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((6450091421:ℚ)/10000000000),((1319029289:ℚ)/2000000000),((97931188473:ℚ)/117250000000),((10705205023:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5572810627:ℚ)/10000000000),((-57380688306569264886831584563246566255981980968885436499:ℚ)/179899743652343750000000000000000000000000000000000000000),((-7428965858208672153350503:ℚ)/23658496000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6509577293:ℚ)/10000000000),((3327333147:ℚ)/5000000000),((32901501603:ℚ)/39400000000),((26971332029:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((169469097:ℚ)/312500000),((-15228902472085862490740804176173270540087447042641930183:ℚ)/47783581250000000000000000000000000000000000000000000000),((-138470372509967504637295261:ℚ)/443596800000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3284530689:ℚ)/5000000000),((268567353:ℚ)/400000000),((49738898957:ℚ)/59575000000),((2174371471:ℚ)/2364000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2634697807:ℚ)/5000000000),((-631272060610597833325529950105463348748513340977473684699:ℚ)/1982272835009765625000000000000000000000000000000000000000),((-880937854231821455362261:ℚ)/2839019520000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6628543719:ℚ)/10000000000),((6773699093:ℚ)/10000000000),((100251068347:ℚ)/120100000000),((54775893651:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2555808483:ℚ)/5000000000),((-107667274979254224321814296946833264228975370168105779423:ℚ)/338344453320312500000000000000000000000000000000000000000),((-182428814468727148911767807:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3344012179:ℚ)/5000000000),((6833212151:ℚ)/10000000000),((16837386109:ℚ)/20175000000),((55192485057:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1237318447:ℚ)/2500000000),((-906676557461423086111897890203892196418625446542380641:ℚ)/2851334326171875000000000000000000000000000000000000000),((-181327447047883022332613543:ℚ)/591462400000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((3373751667:ℚ)/5000000000),((1723180763:ℚ)/2500000000),((50898771671:ℚ)/61000000000),((1544696149:ℚ)/1681250000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1195474477:ℚ)/2500000000),((-225388211804959259022049190852772345276842100233055907171:ℚ)/709315625000000000000000000000000000000000000000000000000),((-11264038534606444031939167:ℚ)/36966400000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((3403490343:ℚ)/5000000000),((7011738581:ℚ)/10000000000),((51285374459:ℚ)/61950000000),((56442170067:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((184357507:ℚ)/400000000),((-2747567854782192220071242824941820730057851921180753019:ℚ)/8844935449218750000000000000000000000000000000000000000),((-178014563317285624018660223:ℚ)/591462400000000000000000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((692593067:ℚ)/1000000000),((7130746063:ℚ)/10000000000),((10411709871:ℚ)/12580000000),((57275222441:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2121748567:ℚ)/5000000000),((-1885538891888953638626127003864521525622877010615139:ℚ)/6075639379882812500000000000000000000000000000000000),((-175798648895703406067244567:ℚ)/591462400000000000000000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((3522437299:ℚ)/5000000000),((7368738309:ℚ)/10000000000),((17610561629:ℚ)/21600000000),((3467127539:ℚ)/3700000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3845770731:ℚ)/10000000000),((-346762893264491277786934828175532732663193114602027803:ℚ)/1166400000000000000000000000000000000000000000000000000),((-514047644094058162239600349:ℚ)/1774387200000000000000000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((7282745357:ℚ)/10000000000),((1040056031:ℚ)/1250000000),((108755689641:ℚ)/144800000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((2899577087:ℚ)/10000000000),((-138743453835859010803239346760975997563853146320832659549:ℚ)/592974100000000000000000000000000000000000000000000000000),((-289131901:ℚ)/1024000000)⟩
theorem valid15 : Valid source24 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((32164193:ℚ)/39062500),((9271832583:ℚ)/10000000000),((473134509:ℚ)/625000000),((72262828081:ℚ)/72400000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-45763581858154343346769681983181670830222565648961:ℚ)/190734863281250000000000000000000000000000000000000),((-289131901:ℚ)/1024000000)⟩
theorem valid16 : Valid source24 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source24 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((2296269081:ℚ)/2500000000),((653773069:ℚ)/500000000),((33371498053:ℚ)/55200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2091333272871141691243327945149726779:ℚ)/21024576000000000000000000000000000000),((-289131901:ℚ)/1024000000)⟩
theorem valid17 : Valid source24 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2383:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source24 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source24 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source24 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source24 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source24 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC30
#check @N11Formalization.C450Source24GroupedC30.bound
#print axioms N11Formalization.C450Source24GroupedC30.valid0
#print axioms N11Formalization.C450Source24GroupedC30.valid1
#print axioms N11Formalization.C450Source24GroupedC30.valid2
#print axioms N11Formalization.C450Source24GroupedC30.valid3
#print axioms N11Formalization.C450Source24GroupedC30.valid4
#print axioms N11Formalization.C450Source24GroupedC30.valid5
#print axioms N11Formalization.C450Source24GroupedC30.valid6
#print axioms N11Formalization.C450Source24GroupedC30.valid7
#print axioms N11Formalization.C450Source24GroupedC30.valid8
#print axioms N11Formalization.C450Source24GroupedC30.valid9
#print axioms N11Formalization.C450Source24GroupedC30.valid10
#print axioms N11Formalization.C450Source24GroupedC30.valid11
#print axioms N11Formalization.C450Source24GroupedC30.valid12
#print axioms N11Formalization.C450Source24GroupedC30.valid13
#print axioms N11Formalization.C450Source24GroupedC30.valid14
#print axioms N11Formalization.C450Source24GroupedC30.valid15
#print axioms N11Formalization.C450Source24GroupedC30.valid16
#print axioms N11Formalization.C450Source24GroupedC30.valid17
#print axioms N11Formalization.C450Source24GroupedC30.bound
#print axioms N11Formalization.C450Source24GroupedC30.endpoint_checks
