import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((6033211137:ℚ)/10000000000),((6551390623:ℚ)/10000000000),((7793211137:ℚ)/26700000000),((8087390623:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((102139493:ℚ)/156250000),((7115947811525787321867003095916201451:ℚ)/312771752755200000000000000000000000000),((-8625120731602689021334933:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1301881751:ℚ)/2000000000),((6789359121:ℚ)/10000000000),((1653881751:ℚ)/5530000000),((2775119707:ℚ)/7120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5423440767:ℚ)/10000000000),((8403182181626491954764874212833690042739512531395091572879:ℚ)/413924860648320000000000000000000000000000000000000000000000),((-356431285806802460607957:ℚ)/2310400000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((674744563:ℚ)/1000000000),((1727082867:ℚ)/2500000000),((283581521:ℚ)/937500000),((2111082867:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4782062901:ℚ)/10000000000),((5234971964186596805420764251648815071787851606250971:ℚ)/271787748750000000000000000000000000000000000000000000),((-90537384025260074659833:ℚ)/577600000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((3433225211:ℚ)/5000000000),((7027296409:ℚ)/10000000000),((4313225211:ℚ)/14300000000),((8563296409:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4429754031:ℚ)/10000000000),((5554684528514597489175329662240662175110379242904372371431:ℚ)/291158613281250000000000000000000000000000000000000000000000),((-2281312249707089705819097:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((279417869:ℚ)/400000000),((3543388109:ℚ)/5000000000),((349817869:ℚ)/1153500000),((4311388109:ℚ)/11440000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((506137907:ℚ)/1250000000),((5152503804787655054170080968769488445580144738019493352131:ℚ)/276681916116320000000000000000000000000000000000000000000000),((-14714850555973215486077:ℚ)/92416000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6879826:ℚ)/9765625),((7146254309:ℚ)/10000000000),((137577216:ℚ)/454296875),((8682254309:ℚ)/23070000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((961383737:ℚ)/2500000000),((5134224213802106991605537898059723524571286814722507915473:ℚ)/276790361345334450000000000000000000000000000000000000000000),((-563510511754356496323:ℚ)/3525390625000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/4),((5:ℚ)/16),((1776108739:ℚ)/2500000000),((3602865363:ℚ)/5000000000),((2216108739:ℚ)/7328125000),((4370865363:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1815587353:ℚ)/5000000000),((1998170388287681335995044303305498740143670778268486342277:ℚ)/108127173708708437500000000000000000000000000000000000000000),((-579271027719079390087047:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((7163926167:ℚ)/10000000000),((1816301377:ℚ)/2500000000),((8923926167:ℚ)/29550000000),((2200301377:ℚ)/5862500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((340397997:ℚ)/1000000000),((404977584327015491201313670996385046001888015410811116863:ℚ)/21992446826921997070312500000000000000000000000000000000000),((-9304122281250062078102773:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((1444683101:ℚ)/2000000000),((1464935739:ℚ)/2000000000),((1796683101:ℚ)/5957500000),((590711913:ℚ)/1576000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((197573753:ℚ)/625000000),((509950955003533766328184580647827903872469999867576856647:ℚ)/27786045155838080000000000000000000000000000000000000000000),((-373596550641730081599357:ℚ)/2310400000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((1456580603:ℚ)/2000000000),((295366013:ℚ)/400000000),((1808580603:ℚ)/6005000000),((356806013:ℚ)/953200000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2898851443:ℚ)/10000000000),((1785488426941278776813584668429961248640636852379734283:ℚ)/97595129838623435000000000000000000000000000000000000000),((-1038859936213492902933:ℚ)/6400000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((367119437:ℚ)/500000000),((375154453:ℚ)/500000000),((455119437:ℚ)/1525000000),((451954453:ℚ)/1201000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2611109371:ℚ)/10000000000),((149164636928754049479771631496041929994305482915677243:ℚ)/8057470149151250000000000000000000000000000000000000000),((-23528784453398034343083:ℚ)/144400000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3730677501:ℚ)/5000000000),((1935237347:ℚ)/2500000000),((4610677501:ℚ)/15725000000),((2319237347:ℚ)/6100000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1913034279:ℚ)/10000000000),((531187122421953238316645610287478490463205672205153798837:ℚ)/28063434319062500000000000000000000000000000000000000000000),((-2370784172448104871423457:ℚ)/14440000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7699267877:ℚ)/10000000000),((398939427:ℚ)/500000000),((9459267877:ℚ)/32400000000),((475739427:ℚ)/1258000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((306010381784640730438188259831461073757698837699415653:ℚ)/16327585780290000000000000000000000000000000000000000000),((-21200313:ℚ)/128000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((3968578241:ℚ)/5000000000),((9880920881:ℚ)/10000000000),((4848578241:ℚ)/20000000000),((11416920881:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((97667466398110290485301485877603856047128258940858893:ℚ)/4081466880000000000000000000000000000000000000000000000),((-21200313:ℚ)/128000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9839599589:ℚ)/10000000000),((3420855587:ℚ)/2500000000),((11599599589:ℚ)/55200000000),((3804855587:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3809011345312538363225613940180428799:ℚ)/121881600000000000000000000000000000000),((-21200313:ℚ)/128000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC21
#check @N11Formalization.C450Source13GroupedC21.bound
#print axioms N11Formalization.C450Source13GroupedC21.valid0
#print axioms N11Formalization.C450Source13GroupedC21.valid1
#print axioms N11Formalization.C450Source13GroupedC21.valid2
#print axioms N11Formalization.C450Source13GroupedC21.valid3
#print axioms N11Formalization.C450Source13GroupedC21.valid4
#print axioms N11Formalization.C450Source13GroupedC21.valid5
#print axioms N11Formalization.C450Source13GroupedC21.valid6
#print axioms N11Formalization.C450Source13GroupedC21.valid7
#print axioms N11Formalization.C450Source13GroupedC21.valid8
#print axioms N11Formalization.C450Source13GroupedC21.valid9
#print axioms N11Formalization.C450Source13GroupedC21.valid10
#print axioms N11Formalization.C450Source13GroupedC21.valid11
#print axioms N11Formalization.C450Source13GroupedC21.valid12
#print axioms N11Formalization.C450Source13GroupedC21.valid13
#print axioms N11Formalization.C450Source13GroupedC21.valid14
#print axioms N11Formalization.C450Source13GroupedC21.bound
#print axioms N11Formalization.C450Source13GroupedC21.endpoint_checks
