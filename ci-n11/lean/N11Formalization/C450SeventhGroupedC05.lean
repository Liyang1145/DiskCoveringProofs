import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((1267159731:ℚ)/2000000000),((6615542423:ℚ)/10000000000),((-19046627269:ℚ)/24800000000),((-13170757041:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5850984503:ℚ)/10000000000),((18618076734635214457470986323236417624175017694529524176703:ℚ)/1517053051200000000000000000000000000000000000000000000000000),((252062157343547105763531299:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((6573361439:ℚ)/10000000000),((1370622419:ℚ)/2000000000),((-3951867257:ℚ)/5150000000),((-68466975829:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2629066901:ℚ)/5000000000),((93102565246726005161302665786890161780999511514019229177:ℚ)/7607364756152343750000000000000000000000000000000000000000),((10097392182320094862190891:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3405459877:ℚ)/5000000000),((6971895103:ℚ)/10000000000),((-20115685309:ℚ)/26700000000),((-35540058647:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4597270231:ℚ)/10000000000),((271080479792635712898693493881740923075165071540561656517767:ℚ)/23427267647653125000000000000000000000000000000000000000000000),((252623913245732250586891379:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3464848691:ℚ)/5000000000),((7031286179:ℚ)/10000000000),((-20293858537:ℚ)/27175000000),((-36193335601:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((8462887:ℚ)/20000000),((94307926651106601138402181838538415227400842674233303858673:ℚ)/8377866632673132324218750000000000000000000000000000000000000),((252719163881318339075053771:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((6989085837:ℚ)/10000000000),((7090676977:ℚ)/10000000000),((-20472030931:ℚ)/27412500000),((-73039944207:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((807386189:ℚ)/2000000000),((41560709646773595992662591607522434186175688423893304630607:ℚ)/3691029280446754074096679687500000000000000000000000000000000),((252814878714303116180106899:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7048474061:ℚ)/10000000000),((284814891:ℚ)/400000000),((-822444673:ℚ)/1106000000),((-73693214671:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3833126909:ℚ)/10000000000),((231778755263017587213946246391873978344928126694122738753:ℚ)/20864502693511706250000000000000000000000000000000000000000),((1213741968998612064292433:ℚ)/8871936000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7078168087:ℚ)/10000000000),((7150067507:ℚ)/10000000000),((-20650202521:ℚ)/27768750000),((-74019848957:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((465908231:ℚ)/1250000000),((231287681650175164278831652817601261540541028253683801265439:ℚ)/20816042760340491628646850585937500000000000000000000000000000),((252911057754395263980439019:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7107862059:ℚ)/10000000000),((7179762673:ℚ)/10000000000),((-20739288019:ℚ)/27887500000),((-74346482649:ℚ)/112025000000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3618457839:ℚ)/10000000000),((604963458885294419044992539019639042958982060956005308232491:ℚ)/54436306504063025146484375000000000000000000000000000000000000),((252959321352581848701745299:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((285502239:ℚ)/400000000),((3604728887:ℚ)/5000000000),((-10414186661:ℚ)/14003125000),((-995641543:ℚ)/1500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((109575877:ℚ)/312500000),((429201809296869580868319542797725286858398722638840147:ℚ)/38613345612001419067382812500000000000000000000000000000),((175213089337576582942699:ℚ)/1280000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7167249837:ℚ)/10000000000),((7239152811:ℚ)/10000000000),((-20917458433:ℚ)/28125000000),((-74999748207:ℚ)/112975000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((339085669:ℚ)/1000000000),((5261338845037939417697544342521520998971598597181926744831611:ℚ)/473250458049774169921875000000000000000000000000000000000000000),((759168590123711325595657553:ℚ)/5544960000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3598471823:ℚ)/5000000000),((3634423893:ℚ)/5000000000),((-10503271679:ℚ)/14121875000),((-37663190053:ℚ)/56725000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((654273571:ℚ)/2000000000),((1259563292446324815670319995518474261695959783693920410261:ℚ)/113275532164380931615829467773437500000000000000000000000000),((189828606351328768363794257:ℚ)/1386240000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3613318701:ℚ)/5000000000),((7298542697:ℚ)/10000000000),((-21095628091:ℚ)/28362500000),((-12608835237:ℚ)/18987500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((786878723:ℚ)/2500000000),((1829612884652072769785226059747805572025400349037957261372899:ℚ)/164512573469808038330078125000000000000000000000000000000000000),((253153536281050953052140579:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((3628165553:ℚ)/5000000000),((1832059387:ℚ)/2500000000),((-5296178161:ℚ)/7120312500),((-37989821083:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3018760129:ℚ)/10000000000),((48159149785504464016854271423755642857056364162244205301:ℚ)/4329570894605255126953125000000000000000000000000000000000),((15825148759473611444081339:ℚ)/115520000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((3643012379:ℚ)/5000000000),((7357932337:ℚ)/10000000000),((-21273797011:ℚ)/28600000000),((-38153136169:ℚ)/57437500000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((36055583:ℚ)/125000000),((2060657643343422640389850596099671598832631493844663970766337:ℚ)/185225339109525000000000000000000000000000000000000000000000000),((253251340076013293782021139:ℚ)/1848320000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7315718359:ℚ)/10000000000),((3693813533:ℚ)/5000000000),((-10681440599:ℚ)/14359375000),((-76632901949:ℚ)/115350000000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2743757589:ℚ)/10000000000),((2739658597662132158812909152961783618263422766602960057267:ℚ)/246219149752628266811370849609375000000000000000000000000000),((63325104014234798846397259:ℚ)/462080000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((734541191:ℚ)/1000000000),((1861754087:ℚ)/2500000000),((-5385262261:ℚ)/7209375000),((-7695953101:ℚ)/11630000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2595655833:ℚ)/10000000000),((5952049416457807938464159724435576563392240052853021899627:ℚ)/527935717287701511383056640625000000000000000000000000000000),((15837432262005977265603139:ℚ)/115520000000000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((462799929:ℚ)/625000000),((3782897111:ℚ)/5000000000),((-10948691333:ℚ)/14537500000),((-1616933073:ℚ)/2462500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2271346169:ℚ)/10000000000),((1077044940380587899062522927253756120200176130607891213173:ℚ)/93151888921086120605468750000000000000000000000000000000000),((63399327289961020142668451:ℚ)/462080000000000000000000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/4),((-11:ℚ)/16),((1504714439:ℚ)/2000000000),((1950836841:ℚ)/2500000000),((-5652510523:ℚ)/7387500000),((-15783858829:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((709689733:ℚ)/5000000000),((170379087937518225594998558612916559503937712431055651461:ℚ)/14064471847979736328125000000000000000000000000000000000000),((17566121:ℚ)/128000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((310444667:ℚ)/400000000),((4139222149:ℚ)/5000000000),((-12017666447:ℚ)/15250000000),((-3261291337:ℚ)/5184000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((955068196502683303867460992528138987942285557247410116143:ℚ)/72715934619140625000000000000000000000000000000000000000000),((17566121:ℚ)/128000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8236197809:ℚ)/10000000000),((10178739923:ℚ)/10000000000),((-29736219769:ℚ)/32400000000),((-86758175899:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((373990747324616093120221828963192192738528075666489987:ℚ)/19929037500000000000000000000000000000000000000000000000),((17566121:ℚ)/128000000)⟩
theorem valid19 : Valid seventh packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((5068222627:ℚ)/5000000000),((13979086929:ℚ)/10000000000),(-1:ℚ),((-53830448897:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((14337366314422841464335983:ℚ)/609408000000000000000000000),((17566121:ℚ)/128000000)⟩
theorem valid20 : Valid seventh packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((4519:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC05
#check @N11Formalization.C450SeventhGroupedC05.bound
#print axioms N11Formalization.C450SeventhGroupedC05.valid0
#print axioms N11Formalization.C450SeventhGroupedC05.valid1
#print axioms N11Formalization.C450SeventhGroupedC05.valid2
#print axioms N11Formalization.C450SeventhGroupedC05.valid3
#print axioms N11Formalization.C450SeventhGroupedC05.valid4
#print axioms N11Formalization.C450SeventhGroupedC05.valid5
#print axioms N11Formalization.C450SeventhGroupedC05.valid6
#print axioms N11Formalization.C450SeventhGroupedC05.valid7
#print axioms N11Formalization.C450SeventhGroupedC05.valid8
#print axioms N11Formalization.C450SeventhGroupedC05.valid9
#print axioms N11Formalization.C450SeventhGroupedC05.valid10
#print axioms N11Formalization.C450SeventhGroupedC05.valid11
#print axioms N11Formalization.C450SeventhGroupedC05.valid12
#print axioms N11Formalization.C450SeventhGroupedC05.valid13
#print axioms N11Formalization.C450SeventhGroupedC05.valid14
#print axioms N11Formalization.C450SeventhGroupedC05.valid15
#print axioms N11Formalization.C450SeventhGroupedC05.valid16
#print axioms N11Formalization.C450SeventhGroupedC05.valid17
#print axioms N11Formalization.C450SeventhGroupedC05.valid18
#print axioms N11Formalization.C450SeventhGroupedC05.valid19
#print axioms N11Formalization.C450SeventhGroupedC05.valid20
#print axioms N11Formalization.C450SeventhGroupedC05.bound
#print axioms N11Formalization.C450SeventhGroupedC05.endpoint_checks
