import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3457308387:ℚ)/5000000000),((3537471927:ℚ)/5000000000),((-37987135051:ℚ)/49600000000),((-8291925161:ℚ)/12518750000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((1069877577:ℚ)/2500000000),((1405653441534671268496753559979060519394866761867083008725317:ℚ)/4895611294474240000000000000000000000000000000000000000000000),((7445399280365736218006198711:ℚ)/11089920000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((697432931:ℚ)/1000000000),((891824587:ℚ)/1250000000),((-9593719631:ℚ)/12518750000),((-1676298793:ℚ)/2527500000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((4086077211:ℚ)/10000000000),((3601774660383943633489733561013784611958367733725708804898433:ℚ)/12533294034013774108886718750000000000000000000000000000000000),((99370642214098309480315453:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((140680709:ℚ)/200000000),((7194244329:ℚ)/10000000000),((-77525176277:ℚ)/101100000000),((-26064779:ℚ)/39250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((38836091:ℚ)/100000000),((3179697871661922642421956974579295151230936162437557631051:ℚ)/11055294008167968750000000000000000000000000000000000000000),((3978753374254310564353613:ℚ)/5914624000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7093735373:ℚ)/10000000000),((3612033119:ℚ)/5000000000),((-38956430547:ℚ)/51025000000),((-12524657:ℚ)/18750000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((1835303217:ℚ)/5000000000),((176889934284269372779417033866130183565534680970222302063:ℚ)/622716424877929687500000000000000000000000000000000000000),((9949096279743507385466927517:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((3561791529:ℚ)/5000000000),((7253886899:ℚ)/10000000000),((-78300529687:ℚ)/102525000000),((-8605374587:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3559565849:ℚ)/10000000000),((6769286809207624119219906745977792265244516233538247858116963:ℚ)/23818946333701464843750000000000000000000000000000000000000000),((7465474514714750716999712879:ℚ)/11089920000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1430685851:ℚ)/2000000000),((7283706329:ℚ)/10000000000),((-78688182277:ℚ)/103000000000),((-3460057553:ℚ)/5173750000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((861277699:ℚ)/2500000000),((332664409433226881930073083454413801291637617256626831830869491:ℚ)/1169991062647937500000000000000000000000000000000000000000000000),((398352971389431451416482573:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3591636991:ℚ)/5000000000),((3656762273:ℚ)/5000000000),((-39537909549:ℚ)/51737500000),((-1242130139:ℚ)/1856250000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((3326888269:ℚ)/10000000000),((493605189622093639721847502011771298768845758239310928228617:ℚ)/1735228043111453247070312500000000000000000000000000000000000),((2490917769926325555342985813:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7213117261:ℚ)/10000000000),((1468668313:ℚ)/2000000000),((-15892688069:ℚ)/20790000000),((-17479351783:ℚ)/26106250000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((640896131:ℚ)/2000000000),((704199624593784007231115222494265996306004462727650867906913:ℚ)/2474441836921982812500000000000000000000000000000000000000000),((9968506407987841362915608733:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((905369889:ℚ)/1250000000),((1843289351:ℚ)/2500000000),((-19962761563:ℚ)/26106250000),((-2196109667:ℚ)/3278125000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1538693959:ℚ)/5000000000),((8709926540434486618514814320703838382114898172525023751460581:ℚ)/30591761181292126846313476562500000000000000000000000000000000),((467499856591590811172279999:ℚ)/693120000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((1454559911:ℚ)/2000000000),((7402972079:ℚ)/10000000000),((-80238637027:ℚ)/104900000000),((-3531679733:ℚ)/5268750000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((1472501427:ℚ)/5000000000),((14603578285184641096412080936709709818556314937921563833182229:ℚ)/51269800930700062500000000000000000000000000000000000000000000),((399125707257468400017392133:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((456414913:ℚ)/625000000),((1486557121:ℚ)/2000000000),((-16125242573:ℚ)/21075000000),((-1109244739:ℚ)/1653906250),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((280657593:ℚ)/1000000000),((2767210844406340621296353598421351159873539998689212945274233:ℚ)/9710927664184472656250000000000000000000000000000000000000000),((38995873570978963897459637:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((733247629:ℚ)/1000000000),((936551159:ℚ)/1250000000),((-10175165067:ℚ)/13231250000),((-1783742887:ℚ)/2670000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((532232741:ℚ)/2000000000),((113370829182668505109327835391703128254735042675886090517:ℚ)/392717093849563598632812500000000000000000000000000000000),((99952911949982775273681693:ℚ)/147865600000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7392147617:ℚ)/10000000000),((237863859:ℚ)/312500000),((-2592230167:ℚ)/3337500000),((-18016442851:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2344123561:ℚ)/10000000000),((3009502240083400011131735034203144444210477186568646031987:ℚ)/10168084916516113281250000000000000000000000000000000000000),((10016997522929657359585589397:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7511474619:ℚ)/10000000000),((7730860969:ℚ)/10000000000),((-84501192597:ℚ)/108700000000),((-18374423857:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((190974147:ℚ)/1250000000),((1622843992855179088540983551293539314669324671473401299847973:ℚ)/5479499582964941406250000000000000000000000000000000000000000),((30017163613190988803270649959:ℚ)/44359680000000000000000000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((7630781657:ℚ)/10000000000),((3984624543:ℚ)/5000000000),((-43800119059:ℚ)/55300000000),((-18732344971:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((515148831566141566222965147398920551367614203494257237432089:ℚ)/1662586056381250000000000000000000000000000000000000000000000),((692329567:ℚ)/1024000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((1573867971:ℚ)/2000000000),((8922278319:ℚ)/10000000000),((-99989618147:ℚ)/114400000000),((-3889603913:ℚ)/6480000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1978859997894182978366412925251526592177287189734682934255903:ℚ)/5116192567200000000000000000000000000000000000000000000000000),((692329567:ℚ)/1024000000)⟩
theorem valid15 : Valid source27 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((8822948653:ℚ)/10000000000),((2706651083:ℚ)/2500000000),((-31186464079:ℚ)/32400000000),((-22308845959:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2077464988129708778430963305069794696743328098029149451:ℚ)/4428675000000000000000000000000000000000000000000000000),((692329567:ℚ)/1024000000)⟩
theorem valid16 : Valid source27 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10728101019:ℚ)/10000000000),((2926335127:ℚ)/2000000000),(-1:ℚ),((-1218447959:ℚ)/2400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1532314884613365918618331:ℚ)/2880000000000000000000000),((692329567:ℚ)/1024000000)⟩
theorem valid17 : Valid source27 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source27 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4101:ℚ)/6400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((4101:ℚ)/6400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((4101:ℚ)/6400) ((4139:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((4139:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source27 nn0 nn1 Qcell ((4101:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((1087:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC04
#check @N11Formalization.C450Source27GroupedC04.bound
#print axioms N11Formalization.C450Source27GroupedC04.valid0
#print axioms N11Formalization.C450Source27GroupedC04.valid1
#print axioms N11Formalization.C450Source27GroupedC04.valid2
#print axioms N11Formalization.C450Source27GroupedC04.valid3
#print axioms N11Formalization.C450Source27GroupedC04.valid4
#print axioms N11Formalization.C450Source27GroupedC04.valid5
#print axioms N11Formalization.C450Source27GroupedC04.valid6
#print axioms N11Formalization.C450Source27GroupedC04.valid7
#print axioms N11Formalization.C450Source27GroupedC04.valid8
#print axioms N11Formalization.C450Source27GroupedC04.valid9
#print axioms N11Formalization.C450Source27GroupedC04.valid10
#print axioms N11Formalization.C450Source27GroupedC04.valid11
#print axioms N11Formalization.C450Source27GroupedC04.valid12
#print axioms N11Formalization.C450Source27GroupedC04.valid13
#print axioms N11Formalization.C450Source27GroupedC04.valid14
#print axioms N11Formalization.C450Source27GroupedC04.valid15
#print axioms N11Formalization.C450Source27GroupedC04.valid16
#print axioms N11Formalization.C450Source27GroupedC04.valid17
#print axioms N11Formalization.C450Source27GroupedC04.bound
#print axioms N11Formalization.C450Source27GroupedC04.endpoint_checks
