import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/4),((13:ℚ)/16),((5255525117:ℚ)/10000000000),((139693557:ℚ)/250000000),((20086575351:ℚ)/25750000000),((2264016241:ℚ)/2480000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8072100629:ℚ)/10000000000),((-1063089028734995354242544178571997669280307:ℚ)/3160527190000000000000000000000000000000000),((-63967183268535887260719:ℚ)/144400000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((2747151863:ℚ)/5000000000),((1456666301:ℚ)/2500000000),((3467151863:ℚ)/4450000000),((23416661913:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7627558441:ℚ)/10000000000),((-1111499498540305630981568765938532579490012281683631304877:ℚ)/3301807619857788085937500000000000000000000000000000000000),((-6289720063696895208769631:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((716623833:ℚ)/1250000000),((5946089039:ℚ)/10000000000),((2689871499:ℚ)/3396875000),((31739719169:ℚ)/35600000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7161468093:ℚ)/10000000000),((-347574920651463392881919283242282769703720788802554223777475327:ℚ)/999563419633200000000000000000000000000000000000000000000000000),((-99765640659353257288798151:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((585230279:ℚ)/1000000000),((6065489531:ℚ)/10000000000),((2187690837:ℚ)/2765000000),((96771363903:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6918927309:ℚ)/10000000000),((-7617316372823910041022795043468462578766809836199448948196229:ℚ)/21917998331859765625000000000000000000000000000000000000000000),((-98886492502748160801507791:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((597159547:ℚ)/1000000000),((1546216969:ℚ)/2500000000),((741159547:ℚ)/937500000),((24580820597:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6669108433:ℚ)/10000000000),((-6555887349232727834625716335433601692018344534528689439:ℚ)/18874149218750000000000000000000000000000000000000000000),((-6124879571011513235864791:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((3045434849:ℚ)/5000000000),((3122274547:ℚ)/5000000000),((11296304547:ℚ)/14181250000),((5505507679:ℚ)/6250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6411136009:ℚ)/10000000000),((-2767788469678458080061351821964973242000860816791053099928459:ℚ)/7855775451660156250000000000000000000000000000000000000000000),((-24387596438208073991532479:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((768812523:ℚ)/1250000000),((6304225189:ℚ)/10000000000),((2846437569:ℚ)/3575000000),((99874927457:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3139385859:ℚ)/5000000000),((-2628952386203061890005734095767472031299407164158670857467757:ℚ)/7464927329623156250000000000000000000000000000000000000000000),((-97100379379869605311006351:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6210126401:ℚ)/10000000000),((3181948143:ℚ)/5000000000),((7650126401:ℚ)/9612500000),((50325325859:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((767994753:ℚ)/1250000000),((-182622683064134385613574142380546182329680917015640938468069973:ℚ)/518778592718100000000000000000000000000000000000000000000000000),((-24162013418598109738982919:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6269748453:ℚ)/10000000000),((6423562511:ℚ)/10000000000),((23129245359:ℚ)/29075000000),((33808770881:ℚ)/38450000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((6006526919:ℚ)/10000000000),((-6763615824658832761245992904255696325290714096066911770150061:ℚ)/19221552871203781250000000000000000000000000000000000000000000),((-96193408266057810148327751:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((1265873289:ℚ)/2000000000),((3241611991:ℚ)/5000000000),((4661619867:ℚ)/5862500000),((51100955883:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5866291321:ℚ)/10000000000),((-23769792249357372553696775615950920320043594034940697591064887:ℚ)/67579483567942773437500000000000000000000000000000000000000000),((-23934110706500383613695511:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((255559219:ℚ)/400000000),((1308576163:ℚ)/2000000000),((313159219:ℚ)/394000000),((20595490119:ℚ)/23450000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5723041919:ℚ)/10000000000),((-274924771144050741636695509841393831052326964437585282129571:ℚ)/781953664957226562500000000000000000000000000000000000000000),((-3811086280884422435540639:ℚ)/9241600000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((80607383:ℚ)/125000000),((6602533123:ℚ)/10000000000),((295822149:ℚ)/372343750),((103752930599:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5576543267:ℚ)/10000000000),((-61795843161522464766153512160928683759330988722041207355716049617:ℚ)/175833567001787850000000000000000000000000000000000000000000000000),((-94815550527179527410427999:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3254098517:ℚ)/5000000000),((3331090507:ℚ)/5000000000),((11922295551:ℚ)/15012500000),((52264176591:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5426528971:ℚ)/10000000000),((-41852614703603229397109371638904607863163959686900873050151459:ℚ)/119134679978788372802734375000000000000000000000000000000000000),((-65340459165582788221079:ℚ)/160000000000000000000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((1313559949:ℚ)/2000000000),((6781463959:ℚ)/10000000000),((4804679847:ℚ)/6100000000),((106079031467:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5272695683:ℚ)/10000000000),((-13956455012704779696454451738862342692841823173099982963548687:ℚ)/40287350745756250000000000000000000000000000000000000000000000),((-93416803891376098426153111:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6686994469:ℚ)/10000000000),((1725182613:ℚ)/2500000000),((8126994469:ℚ)/10325000000),((26907373969:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2476063053:ℚ)/5000000000),((-2618207233088551754238712463857968136483800154780359022085229:ℚ)/7561703552539062500000000000000000000000000000000000000000000),((-5779543581106941001201839:ℚ)/14440000000000000000000000)⟩
theorem valid14 : Valid source29 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6806175479:ℚ)/10000000000),((1754995311:ℚ)/2500000000),((24738526437:ℚ)/31450000000),((27294939043:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4611319309:ℚ)/10000000000),((-24836005306796910313410785963794863068508359843585051794627:ℚ)/71765430886085414886474609375000000000000000000000000000000),((-5719956319801109636937351:ℚ)/14440000000000000000000000)⟩
theorem valid15 : Valid source29 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source29 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((6925343401:ℚ)/10000000000),((7258438513:ℚ)/10000000000),((8365343401:ℚ)/10800000000),((112279700669:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2122686761:ℚ)/5000000000),((-3057606286487137659551234212334076049767049590227774173007401:ℚ)/9070880989050000000000000000000000000000000000000000000000000),((-89584632025626338314247239:ℚ)/231040000000000000000000000)⟩
theorem valid16 : Valid source29 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source29 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((3581821149:ℚ)/5000000000),((572778273:ℚ)/625000000),((12905463447:ℚ)/20000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1702549277:ℚ)/5000000000),((-363031886670225128768452630190984957:ℚ)/1500000000000000000000000000000000000),((-6007471:ℚ)/16000000)⟩
theorem valid17 : Valid source29 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((1133582779:ℚ)/1250000000),((1297149847:ℚ)/1000000000),((1313582779:ℚ)/2300000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-513446053624227917943261:ℚ)/2645000000000000000000000),((-6007471:ℚ)/16000000)⟩
theorem valid18 : Valid source29 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source29 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source29 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC29
#check @N11Formalization.C450Source29GroupedC29.bound
#print axioms N11Formalization.C450Source29GroupedC29.valid0
#print axioms N11Formalization.C450Source29GroupedC29.valid1
#print axioms N11Formalization.C450Source29GroupedC29.valid2
#print axioms N11Formalization.C450Source29GroupedC29.valid3
#print axioms N11Formalization.C450Source29GroupedC29.valid4
#print axioms N11Formalization.C450Source29GroupedC29.valid5
#print axioms N11Formalization.C450Source29GroupedC29.valid6
#print axioms N11Formalization.C450Source29GroupedC29.valid7
#print axioms N11Formalization.C450Source29GroupedC29.valid8
#print axioms N11Formalization.C450Source29GroupedC29.valid9
#print axioms N11Formalization.C450Source29GroupedC29.valid10
#print axioms N11Formalization.C450Source29GroupedC29.valid11
#print axioms N11Formalization.C450Source29GroupedC29.valid12
#print axioms N11Formalization.C450Source29GroupedC29.valid13
#print axioms N11Formalization.C450Source29GroupedC29.valid14
#print axioms N11Formalization.C450Source29GroupedC29.valid15
#print axioms N11Formalization.C450Source29GroupedC29.valid16
#print axioms N11Formalization.C450Source29GroupedC29.valid17
#print axioms N11Formalization.C450Source29GroupedC29.valid18
#print axioms N11Formalization.C450Source29GroupedC29.bound
#print axioms N11Formalization.C450Source29GroupedC29.endpoint_checks
