import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((6225101069:ℚ)/10000000000),((3276762831:ℚ)/5000000000),((409711507:ℚ)/51500000000),((4334898931:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((305484743:ℚ)/500000000),((-66392089985547613916043118537929267522285112424986377822473:ℚ)/2461196828906250000000000000000000000000000000000000000000000),((-206456350497921789547649423:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((3233937419:ℚ)/5000000000),((6674564017:ℚ)/10000000000),((456307949:ℚ)/104900000000),((2046062581:ℚ)/25750000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((69105117:ℚ)/125000000),((-462917496809623860733344522412102679406926558097972006756933:ℚ)/19134668383189062500000000000000000000000000000000000000000000),((-57496981573050030455077823:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((6589113871:ℚ)/10000000000),((3367525757:ℚ)/5000000000),((137422729:ℚ)/52925000000),((3970886129:ℚ)/52450000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((5216690227:ℚ)/10000000000),((-23296452596991149904666391448536473504163816823177641148358113:ℚ)/1019561890261798144531250000000000000000000000000000000000000000),((-241829063970137761348666263:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((1329939769:ℚ)/2000000000),((679551867:ℚ)/1000000000),((9344399:ℚ)/10680000000),((782060231:ℚ)/10585000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((5054423549:ℚ)/10000000000),((-183628015758040389491357640685040199628234769512399022889247:ℚ)/8530519894130700000000000000000000000000000000000000000000000),((-9910745762982537669585223:ℚ)/73932800000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/16),((-1:ℚ)/8),((3355130821:ℚ)/5000000000),((1713992081:ℚ)/2500000000),((-21976243:ℚ)/26700000000),((1924869179:ℚ)/26700000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4887314451:ℚ)/10000000000),((-7218698761547301641445352868809318795662428348976631567:ℚ)/356890556250000000000000000000000000000000000000000000000),((-63430239862431895730210463:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((3385401437:ℚ)/5000000000),((432275961:ℚ)/625000000),((-16827883:ℚ)/6734375000),((1894598563:ℚ)/26937500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((471484239:ℚ)/1000000000),((-36172795952905197914196950528776946247894174888143941:ℚ)/1908850455284118652343750000000000000000000000000000000),((-179837987600583788497047:ℚ)/1280000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((6831323127:ℚ)/10000000000),((6976862429:ℚ)/10000000000),((-450587287:ℚ)/108700000000),((3728676873:ℚ)/54350000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4536389959:ℚ)/10000000000),((-26644338649771483600000230727475726739824815281166976707:ℚ)/1505115823828125000000000000000000000000000000000000000000),((-796991910142407920132695541:ℚ)/5544960000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((6891822967:ℚ)/10000000000),((7037309481:ℚ)/10000000000),((-631928443:ℚ)/109650000000),((3668177033:ℚ)/54825000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4351215543:ℚ)/10000000000),((-3158444399369196164537221007974083212929563298192269983:ℚ)/191618514843750000000000000000000000000000000000000000000),((-271654747941885688379657127:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((6952302941:ℚ)/10000000000),((3579084023:ℚ)/5000000000),((-497252069:ℚ)/55300000000),((3607697059:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1039603809:ℚ)/2500000000),((-302967525199653215522866063531977288581976270735321083:ℚ)/21570456250000000000000000000000000000000000000000000000),((-277658427087408275022102383:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((7073205377:ℚ)/10000000000),((7278954777:ℚ)/10000000000),((-1356864331:ℚ)/112500000000),((3486794623:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3745156471:ℚ)/10000000000),((-104725429241016930771293449510429674207728035646267190293:ℚ)/8898925781250000000000000000000000000000000000000000000000),((-289704638892646345870153847:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3597017213:ℚ)/5000000000),((3760163499:ℚ)/5000000000),((-1040490497:ℚ)/57200000000),((1682982787:ℚ)/28600000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3283259651:ℚ)/10000000000),((-6333228474934491719476339447644390713900697245506055933:ℚ)/877262100000000000000000000000000000000000000000000000000),((-75450722996821124513077167:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7435487:ℚ)/10000000),((7761452441:ℚ)/10000000000),((-2804357323:ℚ)/118200000000),((3124513:ℚ)/59100000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1042233087:ℚ)/5000000000),((-506780812989014358608753504072814251201382696363810371:ℚ)/157176450000000000000000000000000000000000000000000000000),((-326156573170584748567:ℚ)/1848320000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((3838343779:ℚ)/5000000000),((4121526141:ℚ)/5000000000),((-2124578423:ℚ)/61000000000),((1441656221:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1697698696348320063830067928187161242344924317116004471:ℚ)/354657812500000000000000000000000000000000000000000000000),((-1187277:ℚ)/6400000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((8158423857:ℚ)/10000000000),((10163086533:ℚ)/10000000000),((-10009259599:ℚ)/129600000000),((800525381:ℚ)/21600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((88902831797814493242626212602079765739127199380178548389:ℚ)/2550916800000000000000000000000000000000000000000000000000),((-1187277:ℚ)/6400000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((2519717583:ℚ)/2500000000),((559458159:ℚ)/400000000),((-859174477:ℚ)/6400000000),((120282417:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((26618329371008600362653600630854667:ℚ)/327680000000000000000000000000000000),((-1187277:ℚ)/6400000)⟩
theorem valid14 : Valid source34 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source34 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source34 nn0 nn1 Qcell ((2193:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source34 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC14
#check @N11Formalization.C450Source34GroupedC14.bound
#print axioms N11Formalization.C450Source34GroupedC14.valid0
#print axioms N11Formalization.C450Source34GroupedC14.valid1
#print axioms N11Formalization.C450Source34GroupedC14.valid2
#print axioms N11Formalization.C450Source34GroupedC14.valid3
#print axioms N11Formalization.C450Source34GroupedC14.valid4
#print axioms N11Formalization.C450Source34GroupedC14.valid5
#print axioms N11Formalization.C450Source34GroupedC14.valid6
#print axioms N11Formalization.C450Source34GroupedC14.valid7
#print axioms N11Formalization.C450Source34GroupedC14.valid8
#print axioms N11Formalization.C450Source34GroupedC14.valid9
#print axioms N11Formalization.C450Source34GroupedC14.valid10
#print axioms N11Formalization.C450Source34GroupedC14.valid11
#print axioms N11Formalization.C450Source34GroupedC14.valid12
#print axioms N11Formalization.C450Source34GroupedC14.valid13
#print axioms N11Formalization.C450Source34GroupedC14.valid14
#print axioms N11Formalization.C450Source34GroupedC14.bound
#print axioms N11Formalization.C450Source34GroupedC14.endpoint_checks
