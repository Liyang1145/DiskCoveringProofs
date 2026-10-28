import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6316515147:ℚ)/10000000000),((3295418017:ℚ)/5000000000),((-27738762153:ℚ)/49600000000),((-5756515147:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5896768677:ℚ)/10000000000),((128314791374796544722348548686862014856428296971042263255991:ℚ)/8090949606400000000000000000000000000000000000000000000000000),((390926243402732414314897:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((6554143783:ℚ)/10000000000),((6828484281:ℚ)/10000000000),((-57616358529:ℚ)/103000000000),((-5994143783:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2654148429:ℚ)/5000000000),((1927532397750929014441440596042119891335581233552016298526487:ℚ)/121717836098437500000000000000000000000000000000000000000000000),((4682360944630812580297309:ℚ)/43320000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((3395881629:ℚ)/5000000000),((1389460903:ℚ)/2000000000),((-3912382709:ℚ)/7120000000),((-3115881629:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((465375633:ℚ)/1000000000),((40929617463058557663451130105623016413381487293658238459147:ℚ)/2665502452355200000000000000000000000000000000000000000000000),((62271946467088404590407:ℚ)/577600000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((345528493:ℚ)/500000000),((3503356859:ℚ)/5000000000),((-29610211731:ℚ)/54350000000),((-105842831:ℚ)/228437500),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4292323137:ℚ)/10000000000),((2027949080775315273703108457773634952864789282867996899421957:ℚ)/134045866122770117187500000000000000000000000000000000000000000),((388702965774535498084263:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((3484986213:ℚ)/5000000000),((7066122333:ℚ)/10000000000),((-1171668647:ℚ)/2150000000),((-3204986213:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((820096269:ℚ)/2000000000),((13472927021891586475877403679328254212028138156377308203:ℚ)/890403668078613281250000000000000000000000000000000000000),((4662327624098221306067341:ℚ)/43320000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((7029374517:ℚ)/10000000000),((886978303:ℚ)/1250000000),((-7502804727:ℚ)/13825000000),((-6469374517:ℚ)/13884375000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3899772747:ℚ)/10000000000),((1224352544812980484191064052482172806762496840552928469533809:ℚ)/81501963646530102539062500000000000000000000000000000000000000),((194140011192047601499731:ℚ)/1805000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7059075389:ℚ)/10000000000),((57004243:ℚ)/80000000),((-160772729:ℚ)/296200000),((-6499075389:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((59307111:ℚ)/156250000),((759107896715554611101202910083019769582939617538020767:ℚ)/50525932531173128125000000000000000000000000000000000000),((99377395837738774327:ℚ)/924160000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((7088776147:ℚ)/10000000000),((1431046837:ℚ)/2000000000),((-12111421533:ℚ)/22310000000),((-6528776147:ℚ)/14003125000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3688746379:ℚ)/10000000000),((837581225750465661855068814613771978221073177234831203551011:ℚ)/55742777860160537750000000000000000000000000000000000000000000),((62096989939050331876087:ℚ)/577600000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((889809599:ℚ)/1250000000),((3592468929:ℚ)/5000000000),((-30412220361:ℚ)/56012500000),((-819809599:ℚ)/1757812500),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((1789397977:ℚ)/5000000000),((5222348567714712361687679471727943303917315171353440327:ℚ)/347520110508012771606445312500000000000000000000000000000),((1164059178803944630917829:ℚ)/10830000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((3574088663:ℚ)/5000000000),((1442928279:ℚ)/2000000000),((-4072784837:ℚ)/7500000000),((-3294088663:ℚ)/7060937500),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3465513821:ℚ)/10000000000),((269748600058003716449778251726114953454992049197679173094473:ℚ)/17948461816406250000000000000000000000000000000000000000000000),((186208113564205641659029:ℚ)/1732800000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7177877751:ℚ)/10000000000),((7244344797:ℚ)/10000000000),((-61359103173:ℚ)/112975000000),((-6617877751:ℚ)/14181250000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((669712267:ℚ)/2000000000),((1743462356759385249424264100704195752896814407254269774141851:ℚ)/115994144936326073974609375000000000000000000000000000000000000),((4654172616947479423806421:ℚ)/43320000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((7207578067:ℚ)/10000000000),((7274048067:ℚ)/10000000000),((-61626432603:ℚ)/113450000000),((-6647578067:ℚ)/14240625000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3227538993:ℚ)/10000000000),((2848860266596592448822931733773996391244223708974706155244494749:ℚ)/189518484637218860156250000000000000000000000000000000000000000000),((4653146048783314068970741:ℚ)/43320000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((1809319569:ℚ)/2500000000),((1460750241:ℚ)/2000000000),((-589464389:ℚ)/1085000000),((-1669319569:ℚ)/3575000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1211707:ℚ)/3906250),((6089721766429531535084906414185737087881719567941569:ℚ)/405075764843750000000000000000000000000000000000000000),((186084925377390410169589:ℚ)/1732800000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-9:ℚ)/16),((-1:ℚ)/2),((363348919:ℚ)/500000000),((3666727107:ℚ)/5000000000),((-31080543963:ℚ)/57200000000),((-335348919:ℚ)/717968750),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((2971277141:ℚ)/10000000000),((14852532535247191984789483186474043313362491577941462061024181:ℚ)/987868475250800000000000000000000000000000000000000000000000000),((1162775968453742743444981:ℚ)/10830000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7296678379:ℚ)/10000000000),((1472631419:ℚ)/2000000000),((-12485682771:ℚ)/22975000000),((-6736678379:ℚ)/14418750000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2834751479:ℚ)/10000000000),((236941966899218261002957648457423799329397749830888985237:ℚ)/15758025584168209075927734375000000000000000000000000000000),((62001176892091311930903:ℚ)/577600000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1831594569:ℚ)/2500000000),((7422562481:ℚ)/10000000000),((-20987687443:ℚ)/38450000000),((-1691594569:ℚ)/3634375000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((672876207:ℚ)/2500000000),((7276441805606652652851837786172000514771390303099254052570429:ℚ)/480538821780094531250000000000000000000000000000000000000000000),((1549995597170111495207303:ℚ)/14440000000000000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((1477155553:ℚ)/2000000000),((1508274357:ℚ)/2000000000),((-12806469213:ℚ)/23260000000),((-455051851:ℚ)/985000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2379939487:ℚ)/10000000000),((11712849753680550461436267437669520641748906828170645545611:ℚ)/763100274041537500000000000000000000000000000000000000000000),((185993104944637794700981:ℚ)/1732800000000000000000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((7504575561:ℚ)/10000000000),((486186553:ℚ)/625000000),((-1378559659:ℚ)/2462500000),((-113845501:ℚ)/250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1586329757:ℚ)/10000000000),((4407781284332385516376093038556503664641204609001199:ℚ)/279981921386718750000000000000000000000000000000000000),((26071518748600861:ℚ)/243200000000000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((1935541671:ℚ)/2500000000),((825419107:ℚ)/1000000000),((-7044771963:ℚ)/12200000000),((-1795541671:ℚ)/4050000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1225800918481962262786166154268597376826988220845882829269:ℚ)/74461117050000000000000000000000000000000000000000000000000),((3425909:ℚ)/32000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((2054333223:ℚ)/2500000000),((2538704989:ℚ)/2500000000),((-7296114967:ℚ)/10800000000),((-1914333223:ℚ)/5000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((478172092275234771734634001803061893151429397494879163:ℚ)/23619600000000000000000000000000000000000000000000000000),((3425909:ℚ)/32000000)⟩
theorem valid19 : Valid eighth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((2529459941:ℚ)/2500000000),((13955558063:ℚ)/10000000000),((-121760022567:ℚ)/160000000000),((-796486647:ℚ)/2300000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((81731726503777824447187487572328965829885660453273206393729:ℚ)/3385600000000000000000000000000000000000000000000000000000000),((3425909:ℚ)/32000000)⟩
theorem valid20 : Valid eighth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4519:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC08
#check @N11Formalization.C450EighthGroupedC08.bound
#print axioms N11Formalization.C450EighthGroupedC08.valid0
#print axioms N11Formalization.C450EighthGroupedC08.valid1
#print axioms N11Formalization.C450EighthGroupedC08.valid2
#print axioms N11Formalization.C450EighthGroupedC08.valid3
#print axioms N11Formalization.C450EighthGroupedC08.valid4
#print axioms N11Formalization.C450EighthGroupedC08.valid5
#print axioms N11Formalization.C450EighthGroupedC08.valid6
#print axioms N11Formalization.C450EighthGroupedC08.valid7
#print axioms N11Formalization.C450EighthGroupedC08.valid8
#print axioms N11Formalization.C450EighthGroupedC08.valid9
#print axioms N11Formalization.C450EighthGroupedC08.valid10
#print axioms N11Formalization.C450EighthGroupedC08.valid11
#print axioms N11Formalization.C450EighthGroupedC08.valid12
#print axioms N11Formalization.C450EighthGroupedC08.valid13
#print axioms N11Formalization.C450EighthGroupedC08.valid14
#print axioms N11Formalization.C450EighthGroupedC08.valid15
#print axioms N11Formalization.C450EighthGroupedC08.valid16
#print axioms N11Formalization.C450EighthGroupedC08.valid17
#print axioms N11Formalization.C450EighthGroupedC08.valid18
#print axioms N11Formalization.C450EighthGroupedC08.valid19
#print axioms N11Formalization.C450EighthGroupedC08.valid20
#print axioms N11Formalization.C450EighthGroupedC08.bound
#print axioms N11Formalization.C450EighthGroupedC08.endpoint_checks
