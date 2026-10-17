import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((3124488177:ℚ)/5000000000),((408709927:ℚ)/625000000),((-466129781:ℚ)/6200000000),((75511823:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((189209901:ℚ)/312500000),((417269713030085852440879077279408051:ℚ)/3813248000000000000000000000000000000),((-150833738217633728663661457:ℚ)/1386240000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((811023289:ℚ)/1250000000),((6778583939:ℚ)/10000000000),((-8175751817:ℚ)/103000000000),((-11023289:ℚ)/6675000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5477301909:ℚ)/10000000000),((191809080725551459279862427152684283442801410471472149:ℚ)/1772749194335937500000000000000000000000000000000000000),((-3398923138862984828995531:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6727273363:ℚ)/10000000000),((6898150791:ℚ)/10000000000),((-8534452373:ℚ)/106800000000),((-327273363:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1209855831:ℚ)/2500000000),((28572696224401561070687530046447861652704355725419280915161:ℚ)/267910616641406250000000000000000000000000000000000000000000),((-233984783348291145380356659:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((42792343:ℚ)/62500000),((7017689297:ℚ)/10000000000),((-8893067891:ℚ)/108700000000),((-2792343:ℚ)/345625000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2244886951:ℚ)/5000000000),((465489842228717393445828067366565487720473253184769:ℚ)/4382733197188377380371093750000000000000000000000000),((-9461904211732876639339:ℚ)/72200000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((6966250339:ℚ)/10000000000),((7137200913:ℚ)/10000000000),((-9251602739:ℚ)/110600000000),((-188750113:ℚ)/18750000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((41127491:ℚ)/100000000),((9416487603582512264011620073223255873180678095341517169:ℚ)/88995695114135742187500000000000000000000000000000000000),((-250473579011287891312926931:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((1771425269:ℚ)/2500000000),((3628343497:ℚ)/5000000000),((-4805030491:ℚ)/56250000000),((-171425269:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((231246987:ℚ)/625000000),((17343935037802991706362203393686441162028793275629384509:ℚ)/164486643750000000000000000000000000000000000000000000000),((-16170710147725209146700771:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7205128337:ℚ)/10000000000),((922018601:ℚ)/1250000000),((-1246055803:ℚ)/14300000000),((-805128337:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3237686079:ℚ)/10000000000),((18471984132500711455963703362321374138288355808724458192599:ℚ)/175737810797656250000000000000000000000000000000000000000000),((-266998177564217035841410459:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3662266643:ℚ)/5000000000),((7495587539:ℚ)/10000000000),((-10326762617:ℚ)/116300000000),((-154088881:ℚ)/9850000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((675154789:ℚ)/2500000000),((182018231209300411043551534733549160623757921064406079947:ℚ)/1736634531054687500000000000000000000000000000000000000000),((-68818524764718067794937139:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((744391701:ℚ)/1000000000),((7734400111:ℚ)/10000000000),((-11043200333:ℚ)/118200000000),((-104391701:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2030168439:ℚ)/10000000000),((88075350288759799274317531448171593624841510475406993459:ℚ)/838411068750000000000000000000000000000000000000000000000),((-8506775890877693881702633:ℚ)/55449600000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7682624791:ℚ)/10000000000),((8211792607:ℚ)/10000000000),((-12475377821:ℚ)/122000000000),((-427541597:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((45068106158054439586782178278696243471745722340661272153:ℚ)/426902400000000000000000000000000000000000000000000000000),((-20388313:ℚ)/128000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((4079913203:ℚ)/5000000000),((10119077191:ℚ)/10000000000),((-18197231573:ℚ)/129600000000),((-879913203:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3575565046393496740131495113220021092579489720621406726323:ℚ)/32400000000000000000000000000000000000000000000000000000000),((-20388313:ℚ)/128000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((10066530723:ℚ)/10000000000),((1740951081:ℚ)/1250000000),((-3702853243:ℚ)/20000000000),((-3666530723:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((257582721413451706477117390352643762847461872571287594683:ℚ)/2102457600000000000000000000000000000000000000000000000000),((-20388313:ℚ)/128000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC14
#check @N11Formalization.C450Source21GroupedC14.bound
#print axioms N11Formalization.C450Source21GroupedC14.valid0
#print axioms N11Formalization.C450Source21GroupedC14.valid1
#print axioms N11Formalization.C450Source21GroupedC14.valid2
#print axioms N11Formalization.C450Source21GroupedC14.valid3
#print axioms N11Formalization.C450Source21GroupedC14.valid4
#print axioms N11Formalization.C450Source21GroupedC14.valid5
#print axioms N11Formalization.C450Source21GroupedC14.valid6
#print axioms N11Formalization.C450Source21GroupedC14.valid7
#print axioms N11Formalization.C450Source21GroupedC14.valid8
#print axioms N11Formalization.C450Source21GroupedC14.valid9
#print axioms N11Formalization.C450Source21GroupedC14.valid10
#print axioms N11Formalization.C450Source21GroupedC14.valid11
#print axioms N11Formalization.C450Source21GroupedC14.bound
#print axioms N11Formalization.C450Source21GroupedC14.endpoint_checks
