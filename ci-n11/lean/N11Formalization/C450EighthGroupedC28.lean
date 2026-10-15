import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5987233251:ℚ)/10000000000),((3253862167:ℚ)/5000000000),((23233188587:ℚ)/35600000000),((10321586501:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1658943371:ℚ)/2500000000),((-103003094318833605113086319047029343:ℚ)/11279504000000000000000000000000000000),((-32217639361126403740009207:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((3231215107:ℚ)/5000000000),((6745302547:ℚ)/10000000000),((37463366177:ℚ)/55300000000),((21355907641:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2771018603:ℚ)/5000000000),((-34612824060958389979984986337184115333521459584201724197:ℚ)/3170857068750000000000000000000000000000000000000000000000),((-424032798568815203585997:ℚ)/3040000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((6700018539:ℚ)/10000000000),((6864089671:ℚ)/10000000000),((25846734643:ℚ)/37500000000),((21712269013:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4915943681:ℚ)/10000000000),((-430060530706720148926898463859495812850368533042949661:ℚ)/36621093750000000000000000000000000000000000000000000000),((-32231969956096385111891847:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6818810463:ℚ)/10000000000),((6982875561:ℚ)/10000000000),((78846915093:ℚ)/114400000000),((22068626683:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1143453747:ℚ)/2500000000),((-10019196639253387080691186465701009549253859904294184889:ℚ)/850678400000000000000000000000000000000000000000000000000),((-32228004554536483129008383:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((3468800497:ℚ)/5000000000),((7042268063:ℚ)/10000000000),((40076805467:ℚ)/57675000000),((22246804189:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((841209227:ℚ)/2000000000),((-10942179361989056318109910869067428428012304784238471647:ℚ)/899298958227539062500000000000000000000000000000000000000),((-8057795240703488283584863:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3498497879:ℚ)/5000000000),((3550830139:ℚ)/5000000000),((40403476669:ℚ)/58150000000),((11212490417:ℚ)/14418750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((4010352979:ℚ)/10000000000),((-598667985575083782988383998111127113667989479454376467:ℚ)/49157429593750000000000000000000000000000000000000000000),((-8057337881361705264064687:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((7056390199:ℚ)/10000000000),((1432210443:ℚ)/2000000000),((81460292189:ℚ)/117250000000),((4520631329:ℚ)/5815000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3805179453:ℚ)/10000000000),((-13156952630633911526536626577203175817997653110387090687:ℚ)/1079398461914062500000000000000000000000000000000000000000),((-32227565885733896012343407:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((284631373:ℚ)/400000000),((7220443879:ℚ)/10000000000),((3284545103:ℚ)/4728000000),((22781331637:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((448612003:ℚ)/1250000000),((-671523887443719675125777742928270460242708862907083:ℚ)/55046685600000000000000000000000000000000000000000000),((-51561318468929445095703:ℚ)/369664000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((224224317:ℚ)/312500000),((7279835277:ℚ)/10000000000),((2586467487:ℚ)/3723437500),((22959505831:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3359353349:ℚ)/10000000000),((-3938945738551918674295723158363505943132920059008229:ℚ)/322635552573204040527343750000000000000000000000000000),((-31468873043635321203473:ℚ)/225625000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3617285831:ℚ)/5000000000),((458701651:ℚ)/625000000),((41710144141:ℚ)/60050000000),((1446104953:ℚ)/1861718750),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1556807927:ℚ)/5000000000),((-1033440785448124402806044093963590564615550193062367563:ℚ)/84586113330078125000000000000000000000000000000000000000),((-8055617936394399309002127:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((7293964887:ℚ)/10000000000),((7398617301:ℚ)/10000000000),((28024537919:ℚ)/40350000000),((23315851903:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2847488969:ℚ)/10000000000),((-1673310204485993981643244034625290833648873003164836299:ℚ)/136864047656250000000000000000000000000000000000000000000),((-32220861289238082443627183:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((3676678913:ℚ)/5000000000),((7458007939:ℚ)/10000000000),((42363468043:ℚ)/61000000000),((23494023817:ℚ)/30262500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((638650773:ℚ)/2500000000),((-17355593368287711712289112290462443324362512968813960381:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-8054823656708458633758783:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1482550097:ℚ)/2000000000),((1515357699:ℚ)/2000000000),((17076051067:ℚ)/24780000000),((4770073097:ℚ)/6100000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((278050899:ℚ)/1250000000),((-94388470724916007768060857712765963533612963175663703:ℚ)/7925062162500000000000000000000000000000000000000000000),((-1288432215478165681301663:ℚ)/9241600000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((7531534991:ℚ)/10000000000),((30060813:ℚ)/39062500),((86686884901:ℚ)/125800000000),((378229756:ℚ)/483984375),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((268657583:ℚ)/2000000000),((-144960215539302762012870595236589159770447835986790347:ℚ)/12151278759765625000000000000000000000000000000000000000),((-32219101067923320296092767:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((1530063691:ℚ)/2000000000),((1586624957:ℚ)/2000000000),((17598700601:ℚ)/25920000000),((4983874871:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-45668348795434865388838727656526176421108541948324581:ℚ)/4031078400000000000000000000000000000000000000000000000),((-446337:ℚ)/3200000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7887882437:ℚ)/10000000000),((9833481137:ℚ)/10000000000),((90606706807:ℚ)/160000000000),((30620443411:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-24701591117215344393965679647090765335046337820395584603:ℚ)/4800000000000000000000000000000000000000000000000000000000),((-446337:ℚ)/3200000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((195765697:ℚ)/200000000),((2726779883:ℚ)/2000000000),((2230222667:ℚ)/4416000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-25647484293541198487740519375103:ℚ)/21529165824000000000000000000000000),((-446337:ℚ)/3200000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC28
#check @N11Formalization.C450EighthGroupedC28.bound
#print axioms N11Formalization.C450EighthGroupedC28.valid0
#print axioms N11Formalization.C450EighthGroupedC28.valid1
#print axioms N11Formalization.C450EighthGroupedC28.valid2
#print axioms N11Formalization.C450EighthGroupedC28.valid3
#print axioms N11Formalization.C450EighthGroupedC28.valid4
#print axioms N11Formalization.C450EighthGroupedC28.valid5
#print axioms N11Formalization.C450EighthGroupedC28.valid6
#print axioms N11Formalization.C450EighthGroupedC28.valid7
#print axioms N11Formalization.C450EighthGroupedC28.valid8
#print axioms N11Formalization.C450EighthGroupedC28.valid9
#print axioms N11Formalization.C450EighthGroupedC28.valid10
#print axioms N11Formalization.C450EighthGroupedC28.valid11
#print axioms N11Formalization.C450EighthGroupedC28.valid12
#print axioms N11Formalization.C450EighthGroupedC28.valid13
#print axioms N11Formalization.C450EighthGroupedC28.valid14
#print axioms N11Formalization.C450EighthGroupedC28.valid15
#print axioms N11Formalization.C450EighthGroupedC28.valid16
#print axioms N11Formalization.C450EighthGroupedC28.bound
#print axioms N11Formalization.C450EighthGroupedC28.endpoint_checks
