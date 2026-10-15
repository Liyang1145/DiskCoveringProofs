import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((6021568109:ℚ)/10000000000),((6539176621:ℚ)/10000000000),((7301568109:ℚ)/21360000000),((23137529863:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((820259779:ℚ)/1250000000),((599423278176612491896043114292113905111:ℚ)/45307106112000000000000000000000000000000),((-86537508827934526272286689:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1299505159:ℚ)/2000000000),((847131133:ℚ)/1250000000),((1555505159:ℚ)/4424000000),((2981393399:ℚ)/6675000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5453657841:ℚ)/10000000000),((18881534764817934310285555967514422170901188118958793523:ℚ)/1691783607952880859375000000000000000000000000000000000000),((-3547721507475097398525289:ℚ)/23658496000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((3367727573:ℚ)/5000000000),((6895975829:ℚ)/10000000000),((1335909191:ℚ)/3750000000),((24207927487:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((963246817:ℚ)/2000000000),((96856335271815513086064075491924304561866214279063513:ℚ)/9437074609375000000000000000000000000000000000000000000),((-22443166896161967292810801:ℚ)/147865600000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((1713602229:ℚ)/2500000000),((701489671:ℚ)/1000000000),((2033602229:ℚ)/5720000000),((2456469013:ℚ)/5625000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4466575741:ℚ)/10000000000),((1599645624521905406533456451421248671912331281735026629:ℚ)/157963657379150390625000000000000000000000000000000000000),((-46907698397475255899867:ℚ)/307200000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((6973355901:ℚ)/10000000000),((1414871007:ℚ)/2000000000),((8253355901:ℚ)/23070000000),((449873911:ℚ)/1040000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((817859903:ℚ)/2000000000),((1895716873943207663915719515960604896113687035366331309:ℚ)/194883017550000000000000000000000000000000000000000000000),((-272560681060024889923109507:ℚ)/1774387200000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((3516413477:ℚ)/5000000000),((1783452999:ℚ)/2500000000),((4156413477:ℚ)/11630000000),((6230358997:ℚ)/14418750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3887806167:ℚ)/10000000000),((22697248039450165375916918924257005818704430486717360863:ℚ)/2346380965723117828369140625000000000000000000000000000000),((-22780995580460218416075601:ℚ)/147865600000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/16),((3:ℚ)/8),((3546148217:ℚ)/5000000000),((3596633813:ℚ)/5000000000),((4186148217:ℚ)/11725000000),((12549901439:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((367587861:ℚ)/1000000000),((10831868985075519826838193351350773680714071461899488547:ℚ)/1125724339817810058593750000000000000000000000000000000000),((-22848621039051322690779241:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((7151764379:ℚ)/10000000000),((3626360979:ℚ)/5000000000),((8431764379:ℚ)/23640000000),((12639082937:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((431448893:ℚ)/1250000000),((2741575793597966526346921471538967123212866122695476106537:ℚ)/286359984725546836853027343750000000000000000000000000000000),((-91665066022459450739314129:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((7211230827:ℚ)/10000000000),((3656087511:ℚ)/5000000000),((8491230827:ℚ)/23830000000),((12728262533:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3212351369:ℚ)/10000000000),((181795101463791157656719057520845426913153820082364298442543:ℚ)/19079163086131494140625000000000000000000000000000000000000000),((-275807184260551513836707603:ℚ)/1774387200000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((7270695813:ℚ)/10000000000),((230363339:ℚ)/312500000),((8550695813:ℚ)/24020000000),((801090017:ℚ)/1861718750),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1477262207:ℚ)/5000000000),((2207205551864322127086201113884875628929474996830874418081:ℚ)/232684921833571040630340576171875000000000000000000000000000),((-276619411506561180446872883:ℚ)/1774387200000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((7330159373:ℚ)/10000000000),((1498105381:ℚ)/2000000000),((8610159373:ℚ)/24400000000),((5198316143:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2672731297:ℚ)/10000000000),((24438359438061210939945012202002563132475514218435864071:ℚ)/2517959421609765625000000000000000000000000000000000000000),((-92477293426037888324244001:ℚ)/591462400000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1489816469:ℚ)/2000000000),((1932078349:ℚ)/2500000000),((1745816469:ℚ)/5032000000),((6676235047:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((998089603:ℚ)/5000000000),((22740805350220906141014344793163586716849789640266508739:ℚ)/2246368653869628906250000000000000000000000000000000000000),((-3720767254671932723852209:ℚ)/23658496000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((7686912583:ℚ)/10000000000),((7966083057:ℚ)/10000000000),((2988970861:ℚ)/8640000000),((27418249171:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((235799879197365101055767556753676981649497083468686612321:ℚ)/23622085908984375000000000000000000000000000000000000000000),((-162235731:ℚ)/1024000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((7924723417:ℚ)/10000000000),((1973555729:ℚ)/2000000000),((9204723417:ℚ)/32000000000),((6624667187:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((949023233576417520372545708399667:ℚ)/64000000000000000000000000000000000),((-162235731:ℚ)/1024000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((1965335557:ℚ)/2000000000),((427180251:ℚ)/312500000),((2221335557:ℚ)/8832000000),((1391540753:ℚ)/2500000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4509517138640622061073:ℚ)/216678400000000000000000),((-162235731:ℚ)/1024000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC22
#check @N11Formalization.C450Source12GroupedC22.bound
#print axioms N11Formalization.C450Source12GroupedC22.valid0
#print axioms N11Formalization.C450Source12GroupedC22.valid1
#print axioms N11Formalization.C450Source12GroupedC22.valid2
#print axioms N11Formalization.C450Source12GroupedC22.valid3
#print axioms N11Formalization.C450Source12GroupedC22.valid4
#print axioms N11Formalization.C450Source12GroupedC22.valid5
#print axioms N11Formalization.C450Source12GroupedC22.valid6
#print axioms N11Formalization.C450Source12GroupedC22.valid7
#print axioms N11Formalization.C450Source12GroupedC22.valid8
#print axioms N11Formalization.C450Source12GroupedC22.valid9
#print axioms N11Formalization.C450Source12GroupedC22.valid10
#print axioms N11Formalization.C450Source12GroupedC22.valid11
#print axioms N11Formalization.C450Source12GroupedC22.valid12
#print axioms N11Formalization.C450Source12GroupedC22.valid13
#print axioms N11Formalization.C450Source12GroupedC22.valid14
#print axioms N11Formalization.C450Source12GroupedC22.bound
#print axioms N11Formalization.C450Source12GroupedC22.endpoint_checks
