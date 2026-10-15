import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((9:ℚ)/16),((5:ℚ)/8),((5258428601:ℚ)/10000000000),((5601813401:ℚ)/10000000000),((68445857409:ℚ)/103000000000),((7777813401:ℚ)/9920000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1613362111:ℚ)/2000000000),((-230611072826352052385832850017955638755941288749606784287:ℚ)/628423270400000000000000000000000000000000000000000000000),((-432238554214107755861196561:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((1374838697:ℚ)/2500000000),((2921337557:ℚ)/5000000000),((5884516091:ℚ)/8900000000),((4009337557:ℚ)/5150000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((761793429:ℚ)/1000000000),((-6968235211850605456979337050683982390807949112213526773:ℚ)/18994668554687500000000000000000000000000000000000000000),((-106657872654495639133206489:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((5740032243:ℚ)/10000000000),((5963016039:ℚ)/10000000000),((72780290187:ℚ)/108700000000),((8139016039:ℚ)/10680000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7147343181:ℚ)/10000000000),((-115954218759912035481471466983128140301646420417524527011:ℚ)/306520521200000000000000000000000000000000000000000000000),((-424706908247902951092446481:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((2930143031:ℚ)/5000000000),((3041650619:ℚ)/5000000000),((36931287279:ℚ)/55300000000),((4129650619:ℚ)/5435000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6902446373:ℚ)/10000000000),((-3275751057631698355511663613780167787899559302076200187:ℚ)/8670094276843261718750000000000000000000000000000000000),((-105426642136047012065086521:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((299024363:ℚ)/500000000),((1240706721:ℚ)/2000000000),((1249073089:ℚ)/1875000000),((1675906721:ℚ)/2212000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1662542811:ℚ)/2500000000),((-299142585286847854655111620212910800861179669800627:ℚ)/792714267187500000000000000000000000000000000000000),((-16745111421876854099852001:ℚ)/36966400000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((610063857:ℚ)/1000000000),((1565907707:ℚ)/2500000000),((7602574713:ℚ)/11345000000),((703302569:ℚ)/937500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6389613517:ℚ)/10000000000),((-413614982400340435943959159258721328956872274537743:ℚ)/1081943511962890625000000000000000000000000000000000),((-26097292436766596569972089:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6160696317:ℚ)/10000000000),((6323715839:ℚ)/10000000000),((76566266853:ℚ)/114400000000),((8499715839:ℚ)/11345000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6255897177:ℚ)/10000000000),((-498528483123061410129272643980003168105113984116129552033:ℚ)/1305057225458593750000000000000000000000000000000000000000),((-415968185417425617671614881:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((6220742533:ℚ)/10000000000),((1595947237:ℚ)/2500000000),((25702227599:ℚ)/38450000000),((2139947237:ℚ)/2860000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6119684769:ℚ)/10000000000),((-1676489462541796780514418717645989071598020347919477:ℚ)/4392021841796875000000000000000000000000000000000000),((-1363026644128657246480611:ℚ)/3040000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6280777507:ℚ)/10000000000),((3221925227:ℚ)/5000000000),((77646997563:ℚ)/116300000000),((4309925227:ℚ)/5767500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2990401009:ℚ)/5000000000),((-59101646946045472831374966137202508217482986696794421401:ℚ)/154945879765722656250000000000000000000000000000000000000),((-103183106444944757451652569:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((9:ℚ)/16),((5:ℚ)/8),((3170400761:ℚ)/5000000000),((1300780129:ℚ)/2000000000),((39093606849:ℚ)/58625000000),((1735980129:ℚ)/2326000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((291952731:ℚ)/500000000),((-14060221698665063949381675752023194586428503140235387061:ℚ)/36887735167150000000000000000000000000000000000000000000),((-16443406674252024683784801:ℚ)/36966400000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6400814849:ℚ)/10000000000),((6563939799:ℚ)/10000000000),((26242444547:ℚ)/39400000000),((8739939799:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5694224857:ℚ)/10000000000),((-188987518115002174229182284430983870082607343080472591307:ℚ)/496163492993164062500000000000000000000000000000000000000),((-409418326468452214431706161:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6460817753:ℚ)/10000000000),((668398607:ℚ)/1000000000),((79267359777:ℚ)/120100000000),((295332869:ℚ)/394000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((221842697:ℚ)/400000000),((-43122171784463967461303080750895033739921796744610301:ℚ)/114776162162500000000000000000000000000000000000000000),((-4055288603465533341490689:ℚ)/9241600000000000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((6580793297:ℚ)/10000000000),((6803991323:ℚ)/10000000000),((80347139673:ℚ)/122000000000),((8979991323:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2619309069:ℚ)/5000000000),((-247893512009452650640068190010875962747455860261602777183:ℚ)/660448372881250000000000000000000000000000000000000000000),((-402058322661965365502229369:ℚ)/924160000000000000000000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((1340146019:ℚ)/2000000000),((7043886359:ℚ)/10000000000),((16285314171:ℚ)/25160000000),((9219886359:ℚ)/12200000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((4913959851:ℚ)/10000000000),((-652638923192379761732832683796946124163009123016359793131:ℚ)/1784638112500000000000000000000000000000000000000000000000),((-1091105415203248782166281:ℚ)/2560000000000000000000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((3470247303:ℚ)/5000000000),((364181947:ℚ)/500000000),((13930741909:ℚ)/21600000000),((472981947:ℚ)/629000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4196711711:ℚ)/10000000000),((-414872104535994546254385949799904918857159575881877:ℚ)/1134995118750000000000000000000000000000000000000000),((-966002101302001163894649:ℚ)/2310400000000000000000000)⟩
theorem valid14 : Valid source35 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((718012453:ℚ)/1000000000),((9197766913:ℚ)/10000000000),((8574112077:ℚ)/16000000000),((11373766913:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((333955397:ℚ)/1000000000),((-70007692328943493054891014308699065635292896590530331:ℚ)/283435200000000000000000000000000000000000000000000000),((-395156606463489:ℚ)/972800000000000)⟩
theorem valid15 : Valid source35 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((4546742651:ℚ)/5000000000),((6507138371:ℚ)/5000000000),((17160227953:ℚ)/36800000000),((7595138371:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-444540854841412320476961802144079231:ℚ)/2944000000000000000000000000000000000),((-26238057:ℚ)/64000000)⟩
theorem valid16 : Valid source35 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC26
#check @N11Formalization.C450Source35GroupedC26.bound
#print axioms N11Formalization.C450Source35GroupedC26.valid0
#print axioms N11Formalization.C450Source35GroupedC26.valid1
#print axioms N11Formalization.C450Source35GroupedC26.valid2
#print axioms N11Formalization.C450Source35GroupedC26.valid3
#print axioms N11Formalization.C450Source35GroupedC26.valid4
#print axioms N11Formalization.C450Source35GroupedC26.valid5
#print axioms N11Formalization.C450Source35GroupedC26.valid6
#print axioms N11Formalization.C450Source35GroupedC26.valid7
#print axioms N11Formalization.C450Source35GroupedC26.valid8
#print axioms N11Formalization.C450Source35GroupedC26.valid9
#print axioms N11Formalization.C450Source35GroupedC26.valid10
#print axioms N11Formalization.C450Source35GroupedC26.valid11
#print axioms N11Formalization.C450Source35GroupedC26.valid12
#print axioms N11Formalization.C450Source35GroupedC26.valid13
#print axioms N11Formalization.C450Source35GroupedC26.valid14
#print axioms N11Formalization.C450Source35GroupedC26.valid15
#print axioms N11Formalization.C450Source35GroupedC26.valid16
#print axioms N11Formalization.C450Source35GroupedC26.bound
#print axioms N11Formalization.C450Source35GroupedC26.endpoint_checks
