import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((91565529:ℚ)/156250000),((3195578533:ℚ)/5000000000),((102565529:ℚ)/166875000),((38991363863:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3451318457:ℚ)/5000000000),((-4298051841680312515254183983:ℚ)/232350622558593750000000000000),((-201540051864350967921427:ℚ)/902500000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6335892661:ℚ)/10000000000),((265158451:ℚ)/400000000),((7039892661:ℚ)/11060000000),((3223942961:ℚ)/4272000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2925380267:ℚ)/5000000000),((-39066239553609949434353806056271367998053359899066341:ℚ)/1691123770000000000000000000000000000000000000000000000),((-827118609559515498318599187:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((6573705977:ℚ)/10000000000),((3373927829:ℚ)/5000000000),((7277705977:ℚ)/11250000000),((5850458017:ℚ)/7900000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1051446103:ℚ)/2000000000),((-14958498551034836109896104665974264573232852408020899:ℚ)/593261718750000000000000000000000000000000000000000000),((-827935295373553378655171963:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6692604683:ℚ)/10000000000),((6866745237:ℚ)/10000000000),((568969591:ℚ)/880000000),((27738065869:ℚ)/37500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1234142523:ℚ)/2500000000),((-1958974205853863545710880729440219989873553685829:ℚ)/77440000000000000000000000000000000000000000000000),((-828346492781022556256136083:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((170287461:ℚ)/250000000),((873203781:ℚ)/1250000000),((187887461:ℚ)/290750000),((10565241591:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4595553857:ℚ)/10000000000),((-584594935557657258678319856942579907969695091343:ℚ)/23042545122070312500000000000000000000000000000000),((-517974746295752145622387:ℚ)/2310400000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((6930387491:ℚ)/10000000000),((704507111:ℚ)/1000000000),((7634387491:ℚ)/11725000000),((8517578221:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((33833853:ℚ)/80000000),((-5684030745866934089838424916260641957244017722135471:ℚ)/215879692382812500000000000000000000000000000000000000),((-829174599860416430213928707:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1747457581:ℚ)/2500000000),((7104510911:ℚ)/10000000000),((641152527:ℚ)/985000000),((85829620021:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2017218233:ℚ)/5000000000),((-7869324193914577810336560683811450039262718784527:ℚ)/298647382812500000000000000000000000000000000000000),((-51836426070109388914455267:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((1409854413:ℚ)/2000000000),((7163949677:ℚ)/10000000000),((1550654413:ℚ)/2383000000),((86483446447:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((478789799:ℚ)/1250000000),((-1338094489145171790025971792100233743899378118348831:ℚ)/50746184576250000000000000000000000000000000000000000),((-33183660428779448045239843:ℚ)/147865600000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((355435637:ℚ)/500000000),((7223387433:ℚ)/10000000000),((390635637:ℚ)/600500000),((87137261763:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1807647307:ℚ)/5000000000),((-446363286254897400430590775829749035993536907133:ℚ)/16917222666015625000000000000000000000000000000000),((-2074501701796899553716243:ℚ)/9241600000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((3584076187:ℚ)/5000000000),((7282824203:ℚ)/10000000000),((3936076187:ℚ)/6052500000),((87791066233:ℚ)/120100000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((423410581:ℚ)/1250000000),((-270993052652173993047867432893320639065641264807369:ℚ)/10264803574218750000000000000000000000000000000000000),((-207502581795503999225566643:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((451724437:ℚ)/625000000),((7342260009:ℚ)/10000000000),((495724437:ℚ)/762500000),((29481620033:ℚ)/40350000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1571729691:ℚ)/5000000000),((-14637199818382420993323388504481333874124699821613:ℚ)/554152832031250000000000000000000000000000000000000),((-3243048633486358744142643:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3643514309:ℚ)/5000000000),((7461128819:ℚ)/10000000000),((1331838103:ℚ)/2065000000),((89752417009:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2879799601:ℚ)/10000000000),((-70397288079708004980498025615485608385360659981007:ℚ)/2751757695312500000000000000000000000000000000000000),((-575090754675034195784187:ℚ)/2560000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((7405900983:ℚ)/10000000000),((1515998807:ℚ)/2000000000),((477052999:ℚ)/740000000),((2601712411:ℚ)/3540000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1132448687:ℚ)/5000000000),((-12671813589879989915582226073488289457487903311:ℚ)/494658203125000000000000000000000000000000000000),((-830853678891472985488238683:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((7524769647:ℚ)/10000000000),((3908857159:ℚ)/5000000000),((8228769647:ℚ)/12960000000),((46837428749:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1408197767:ℚ)/10000000000),((-2426293543331908342845401505370316251827818127629981:ℚ)/100776960000000000000000000000000000000000000000000000),((-831278215053362003850667723:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((3881248261:ℚ)/5000000000),((1214887439:ℚ)/1250000000),((4233248261:ℚ)/8000000000),((14323761829:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-1004153663178644410820994088043840825086941240892087:ℚ)/120000000000000000000000000000000000000000000000000000),((-57586419:ℚ)/256000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9663923151:ℚ)/10000000000),((3380181221:ℚ)/2500000000),((10367923151:ℚ)/22080000000),((39101993431:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((654141182759598713261111:ℚ)/243763200000000000000000000),((-57586419:ℚ)/256000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC27
#check @N11Formalization.C450Source13GroupedC27.bound
#print axioms N11Formalization.C450Source13GroupedC27.valid0
#print axioms N11Formalization.C450Source13GroupedC27.valid1
#print axioms N11Formalization.C450Source13GroupedC27.valid2
#print axioms N11Formalization.C450Source13GroupedC27.valid3
#print axioms N11Formalization.C450Source13GroupedC27.valid4
#print axioms N11Formalization.C450Source13GroupedC27.valid5
#print axioms N11Formalization.C450Source13GroupedC27.valid6
#print axioms N11Formalization.C450Source13GroupedC27.valid7
#print axioms N11Formalization.C450Source13GroupedC27.valid8
#print axioms N11Formalization.C450Source13GroupedC27.valid9
#print axioms N11Formalization.C450Source13GroupedC27.valid10
#print axioms N11Formalization.C450Source13GroupedC27.valid11
#print axioms N11Formalization.C450Source13GroupedC27.valid12
#print axioms N11Formalization.C450Source13GroupedC27.valid13
#print axioms N11Formalization.C450Source13GroupedC27.valid14
#print axioms N11Formalization.C450Source13GroupedC27.valid15
#print axioms N11Formalization.C450Source13GroupedC27.bound
#print axioms N11Formalization.C450Source13GroupedC27.endpoint_checks
