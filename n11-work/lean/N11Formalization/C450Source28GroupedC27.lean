import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/8),((11:ℚ)/16),((675961953:ℚ)/1250000000),((5736102589:ℚ)/10000000000),((883961953:ℚ)/1287500000),((80377128479:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7791103947:ℚ)/10000000000),((-138112692971355727052483160000489:ℚ)/533558105468750000000000000000000),((-157403408721139630499143113:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((45176377:ℚ)/80000000),((5975445271:ℚ)/10000000000),((58488377:ℚ)/85440000),((83009897981:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7332061137:ℚ)/10000000000),((-3934213527079598711119520825768306914290218747:ℚ)/15227330400000000000000000000000000000000000000),((-155903388460400757400046673:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((5886265437:ℚ)/10000000000),((6095067761:ℚ)/10000000000),((7550265437:ℚ)/10870000000),((84325745371:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6848584251:ℚ)/10000000000),((-6469294336299567590424636715882120751861742272254274669:ℚ)/24081853181250000000000000000000000000000000000000000000),((-155256301899472847408263713:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6005829073:ℚ)/10000000000),((3107329977:ℚ)/5000000000),((7669829073:ℚ)/11060000000),((42820629747:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6595946927:ℚ)/10000000000),((-141685558616980740746833896226626469794657216380170203:ℚ)/528476178125000000000000000000000000000000000000000000),((-106968041350491430092617:ℚ)/256000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((1531341119:ℚ)/2500000000),((6334223407:ℚ)/10000000000),((1947341119:ℚ)/2812500000),((86956457477:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3167428601:ℚ)/5000000000),((-12401480985237382972262741432577166148896367725714487:ℚ)/46348571777343750000000000000000000000000000000000000),((-153649645871428887497168097:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((780609137:ℚ)/1250000000),((6393994813:ℚ)/10000000000),((988609137:ℚ)/1418125000),((87613942943:ℚ)/112500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((303209823:ℚ)/500000000),((-4853003989877222412833132041665421188449750833450827:ℚ)/17824754499816894531250000000000000000000000000000000),((-153301621452339581948922057:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6304617787:ℚ)/10000000000),((6453759571:ℚ)/10000000000),((612970599:ℚ)/880000000),((88271355281:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1481215123:ℚ)/2500000000),((-4211791884199485884906630090343334684127168116311:ℚ)/15488000000000000000000000000000000000000000000000),((-152884416249164979100978473:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((3182178141:ℚ)/5000000000),((3256758923:ℚ)/5000000000),((4014178141:ℚ)/5767500000),((44464348153:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((11565187:ℚ)/20000000),((-244265832329561031543503916191666125699234497265281853:ℚ)/899298958227539062500000000000000000000000000000000000),((-38115693412110420466922937:ℚ)/92416000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((200752773:ℚ)/312500000),((32866349:ℚ)/50000000),((252752773:ℚ)/363437500),((447929839:ℚ)/576750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1409292547:ℚ)/2500000000),((-3255947192085030920073177821444795668209418686787:ℚ)/12001325584411621093750000000000000000000000000000),((-3800917348508196147753:ℚ)/9241600000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((6483815297:ℚ)/10000000000),((1658253897:ℚ)/2500000000),((8147815297:ℚ)/11725000000),((22560792867:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1097667249:ℚ)/2000000000),((-292497197736979495141789941632366920121686679641358863:ℚ)/1079398461914062500000000000000000000000000000000000000),((-9475386088557824176920977:ℚ)/23104000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((408971007:ℚ)/625000000),((6692755361:ℚ)/10000000000),((512971007:ℚ)/738750000),((90900308971:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((13339507:ℚ)/25000000),((-56836205727192430509340382006541099918414487734359:ℚ)/209986441040039062500000000000000000000000000000000),((-151171224356212799325245313:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6603251321:ℚ)/10000000000),((6812217439:ℚ)/10000000000),((8267251321:ℚ)/12010000000),((92214391829:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2589619739:ℚ)/5000000000),((-8622581397697300758192402448377849027628228757592163993:ℚ)/32481067518750000000000000000000000000000000000000000000),((-150223318462517746231920513:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((1344533091:ℚ)/2000000000),((6931657143:ℚ)/10000000000),((1677333091:ℚ)/2440000000),((93528228573:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((485243837:ℚ)/1000000000),((-24054750011862678962503633454787384532735944130374121:ℚ)/90792400000000000000000000000000000000000000000000000),((-149322372239651076233652497:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1368411747:ℚ)/2000000000),((3585236767:ℚ)/5000000000),((1701211747:ℚ)/2516000000),((48077604437:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((4504049573:ℚ)/10000000000),((-6354470633107490346698062416903237782639854673741233:ℚ)/24885818900000000000000000000000000000000000000000000),((-36834481062037997442646017:ℚ)/92416000000000000000000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((7080786551:ℚ)/10000000000),((7409212123:ℚ)/10000000000),((8744786551:ℚ)/12960000000),((98781333353:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3717793191:ℚ)/10000000000),((-128310057488277901328515847468347912354934798901872807:ℚ)/503884800000000000000000000000000000000000000000000000),((-145411896810745150071984537:ℚ)/369664000000000000000000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((7319441839:ℚ)/10000000000),((9316990521:ℚ)/10000000000),((8983441839:ℚ)/16000000000),((1478603651:ℚ)/1600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2725616869:ℚ)/10000000000),((-262752966639927417052164219918988342552705800898385301:ℚ)/1600000000000000000000000000000000000000000000000000000),((-2490878602444371:ℚ)/6400000000000000)⟩
theorem valid15 : Valid source28 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9226697871:ℚ)/10000000000),((1312609887:ℚ)/1000000000),((10890697871:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-175104336194751696456327:ℚ)/1692800000000000000000000),((-49922823:ℚ)/128000000)⟩
theorem valid16 : Valid source28 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source28 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source28 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source28 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC27
#check @N11Formalization.C450Source28GroupedC27.bound
#print axioms N11Formalization.C450Source28GroupedC27.valid0
#print axioms N11Formalization.C450Source28GroupedC27.valid1
#print axioms N11Formalization.C450Source28GroupedC27.valid2
#print axioms N11Formalization.C450Source28GroupedC27.valid3
#print axioms N11Formalization.C450Source28GroupedC27.valid4
#print axioms N11Formalization.C450Source28GroupedC27.valid5
#print axioms N11Formalization.C450Source28GroupedC27.valid6
#print axioms N11Formalization.C450Source28GroupedC27.valid7
#print axioms N11Formalization.C450Source28GroupedC27.valid8
#print axioms N11Formalization.C450Source28GroupedC27.valid9
#print axioms N11Formalization.C450Source28GroupedC27.valid10
#print axioms N11Formalization.C450Source28GroupedC27.valid11
#print axioms N11Formalization.C450Source28GroupedC27.valid12
#print axioms N11Formalization.C450Source28GroupedC27.valid13
#print axioms N11Formalization.C450Source28GroupedC27.valid14
#print axioms N11Formalization.C450Source28GroupedC27.valid15
#print axioms N11Formalization.C450Source28GroupedC27.valid16
#print axioms N11Formalization.C450Source28GroupedC27.bound
#print axioms N11Formalization.C450Source28GroupedC27.endpoint_checks
