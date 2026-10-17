import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((1493739389:ℚ)/2500000000),((32487629:ℚ)/50000000),((5361218167:ℚ)/13350000000),((265813403:ℚ)/496000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6661953433:ℚ)/10000000000),((11122300239740868204511:ℚ)/1001250000000000000000000),((-5153557684039411843664459:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6451030323:ℚ)/10000000000),((6735455151:ℚ)/10000000000),((22873090969:ℚ)/55300000000),((18276062019:ℚ)/35600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5570474317:ℚ)/10000000000),((380138750551008639167433317625188171:ℚ)/45871350000000000000000000000000000000),((-84234411938601277389984891:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((6689011249:ℚ)/10000000000),((6854408921:ℚ)/10000000000),((23587033747:ℚ)/56250000000),((55660862447:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((247326957:ℚ)/500000000),((111712671813358162792572203058406771:ℚ)/15820312500000000000000000000000000000),((-85124679105970738963670179:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((6807989493:ℚ)/10000000000),((3486677953:ℚ)/5000000000),((23943968479:ℚ)/57200000000),((28246745671:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4605952221:ℚ)/10000000000),((112997041065769469983511789679058019:ℚ)/16359200000000000000000000000000000000),((-85570199285325923658561771:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((1385392027:ℚ)/2000000000),((7032826959:ℚ)/10000000000),((4860176081:ℚ)/11535000000),((56909788713:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2120103:ℚ)/5000000),((1759410528688201002908365770075060624507334182653639466750783:ℚ)/276681916116320000000000000000000000000000000000000000000000000),((-3440639166208623387492491:ℚ)/18483200000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((3493221361:ℚ)/5000000000),((7092296439:ℚ)/10000000000),((12239664083:ℚ)/29075000000),((19108691691:ℚ)/38450000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((4045775227:ℚ)/10000000000),((24217642632287605253620995583035450279025664392622155111581:ℚ)/3844310574240756250000000000000000000000000000000000000000000),((-21559741723647832218635459:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/8),((7:ℚ)/16),((7045923547:ℚ)/10000000000),((223492637:ℚ)/312500000),((3522538663:ℚ)/8375000000),((1804448459:ℚ)/3634375000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1921045087:ℚ)/5000000000),((1261414832067507571596675009140155103055690066177503183:ℚ)/202027314556589126586914062500000000000000000000000000000),((-86462020055629140099046411:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((7105402653:ℚ)/10000000000),((450701927:ℚ)/625000000),((24836207959:ℚ)/59100000000),((3634913489:ℚ)/7328125000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1813794107:ℚ)/5000000000),((531891288132216597039781002863102306708780344422225988493:ℚ)/85907995417664051055908203125000000000000000000000000000000),((-86685138793256295598565211:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((7164880081:ℚ)/10000000000),((3635347909:ℚ)/5000000000),((25014640243:ℚ)/59575000000),((29287435363:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((425027311:ℚ)/1250000000),((27000941797915846081214611488773307130562471926337748545877391:ℚ)/4395839175044696250000000000000000000000000000000000000000000000),((-86908323255102470132024419:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((225761121:ℚ)/312500000),((3665079689:ℚ)/5000000000),((787283363:ℚ)/1876562500),((29495557823:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3157197541:ℚ)/10000000000),((145264234679891572156819327190444266415977898108597559626513:ℚ)/23826935995757674560546875000000000000000000000000000000000000),((-85089427333003995372489:ℚ)/451250000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((455239379:ℚ)/625000000),((148981647:ℚ)/200000000),((1585718137:ℚ)/3812500000),((1196471529:ℚ)/2402000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((11306957:ℚ)/39062500),((415193370173961138986907711622749728760596104413289551:ℚ)/64459761193210000000000000000000000000000000000000000000),((-341230038795695218182239:ℚ)/1805000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((3701386901:ℚ)/5000000000),((7568000007:ℚ)/10000000000),((12864160703:ℚ)/30975000000),((60656000049:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((142696793:ℚ)/625000000),((5538720337943270978120130385631018702392559068733239478631911:ℚ)/871108249252500000000000000000000000000000000000000000000000000),((-21950430296933225520210379:ℚ)/115520000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((235053487:ℚ)/312500000),((1921728147:ℚ)/2500000000),((815160461:ℚ)/1965625000),((5124032343:ℚ)/10325000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1436582167:ℚ)/10000000000),((3342409434518667377537943689836430400935358808210152057:ℚ)/531595784341373443603515625000000000000000000000000000000),((-86180486391177580637501:ℚ)/451250000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((7640643681:ℚ)/10000000000),((3962361711:ℚ)/5000000000),((26441931043:ℚ)/64800000000),((31576531977:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((145675030955292266644677666386099149:ℚ)/20995200000000000000000000000000000000),((-24527221:ℚ)/128000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((3939245911:ℚ)/5000000000),((982667779:ℚ)/1000000000),((13577737733:ℚ)/40000000000),((7646674453:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((86254890423010439534171063273570327:ℚ)/6000000000000000000000000000000000000),((-24527221:ℚ)/128000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((1956136131:ℚ)/2000000000),((6814485303:ℚ)/5000000000),((6572408393:ℚ)/22080000000),((51541397121:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5536953608954834069837639:ℚ)/243763200000000000000000000),((-24527221:ℚ)/128000000)⟩
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
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
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
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC23
#check @N11Formalization.C450Source13GroupedC23.bound
#print axioms N11Formalization.C450Source13GroupedC23.valid0
#print axioms N11Formalization.C450Source13GroupedC23.valid1
#print axioms N11Formalization.C450Source13GroupedC23.valid2
#print axioms N11Formalization.C450Source13GroupedC23.valid3
#print axioms N11Formalization.C450Source13GroupedC23.valid4
#print axioms N11Formalization.C450Source13GroupedC23.valid5
#print axioms N11Formalization.C450Source13GroupedC23.valid6
#print axioms N11Formalization.C450Source13GroupedC23.valid7
#print axioms N11Formalization.C450Source13GroupedC23.valid8
#print axioms N11Formalization.C450Source13GroupedC23.valid9
#print axioms N11Formalization.C450Source13GroupedC23.valid10
#print axioms N11Formalization.C450Source13GroupedC23.valid11
#print axioms N11Formalization.C450Source13GroupedC23.valid12
#print axioms N11Formalization.C450Source13GroupedC23.valid13
#print axioms N11Formalization.C450Source13GroupedC23.valid14
#print axioms N11Formalization.C450Source13GroupedC23.valid15
#print axioms N11Formalization.C450Source13GroupedC23.bound
#print axioms N11Formalization.C450Source13GroupedC23.endpoint_checks
