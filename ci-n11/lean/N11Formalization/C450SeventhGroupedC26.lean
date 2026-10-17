import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((3023584353:ℚ)/5000000000),((6560451467:ℚ)/10000000000),((28812259177:ℚ)/53400000000),((6944451467:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1626666961:ℚ)/2500000000),((-31138080086049824726592508740448859:ℚ)/19034163000000000000000000000000000000),((-3621475437184947703075771:ℚ)/34656000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3261185133:ℚ)/5000000000),((6798021871:ℚ)/10000000000),((30950666197:ℚ)/55300000000),((7182021871:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5390307323:ℚ)/10000000000),((-4248102661346701628494818908081402978841800271103363831:ℚ)/1585428534375000000000000000000000000000000000000000000000),((-3640790714694113319922291:ℚ)/34656000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((1689990163:ℚ)/2500000000),((6916805289:ℚ)/10000000000),((16009911467:ℚ)/28125000000),((7300805289:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1186538727:ℚ)/2500000000),((-73087718661905784568897901999586042810803674387686601:ℚ)/23174285888671875000000000000000000000000000000000000000),((-304224524711514672388337:ℚ)/2888000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((3439376777:ℚ)/5000000000),((3488098289:ℚ)/5000000000),((32554390993:ℚ)/56725000000),((3680098289:ℚ)/5625000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4391834751:ℚ)/10000000000),((-1928298077918846459026997478298042328809278812211275257:ℚ)/570392143994140625000000000000000000000000000000000000000),((-1218569193325268397025017:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((3469074733:ℚ)/5000000000),((1758896899:ℚ)/2500000000),((32821672597:ℚ)/57200000000),((1854896899:ℚ)/2836250000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((4204278331:ℚ)/10000000000),((-556164027048041624170114069355683993497307474228891:ℚ)/163592000000000000000000000000000000000000000000000000),((-1219409865188879886626897:ℚ)/11552000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((6997545031:ℚ)/10000000000),((7094978351:ℚ)/10000000000),((66177905279:ℚ)/115350000000),((575306027:ℚ)/880000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4008501191:ℚ)/10000000000),((-12294805237875581479482344519731993952373794288488703453:ℚ)/3597195832910156250000000000000000000000000000000000000000),((-4881015814245309166867353:ℚ)/46208000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((220529383:ℚ)/312500000),((447148053:ℚ)/625000000),((2084764447:ℚ)/3634375000),((157049351:ℚ)/240312500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3803230253:ℚ)/10000000000),((-20613654165709434771686934492143043709023852307967:ℚ)/6000662792205810546875000000000000000000000000000000),((-4769927572198160220597:ℚ)/45125000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((9:ℚ)/16),((5:ℚ)/8),((7116335151:ℚ)/10000000000),((7213759093:ℚ)/10000000000),((67247016359:ℚ)/117250000000),((7597759093:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3586831961:ℚ)/10000000000),((-266129972298436027474299770211053693013893995153721573:ℚ)/77099890136718750000000000000000000000000000000000000000),((-14663428560454591653909019:ℚ)/138624000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((9:ℚ)/16),((5:ℚ)/8),((7175729723:ℚ)/10000000000),((1810863531:ℚ)/2500000000),((67781567507:ℚ)/117725000000),((1906863531:ℚ)/2931250000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((3357151057:ℚ)/10000000000),((-4532493097944184689708734193098409648619409610688342003:ℚ)/1274665195666503906250000000000000000000000000000000000000),((-4891226873082605755502017:ℚ)/46208000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7205426891:ℚ)/10000000000),((3636574547:ℚ)/5000000000),((68048842019:ℚ)/118200000000),((3828574547:ℚ)/5886250000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1618225537:ℚ)/5000000000),((-4596799141369243150863862378815411813428172647456359411:ℚ)/1290156693750000000000000000000000000000000000000000000000),((-4892940674675316090900513:ℚ)/46208000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((7235123981:ℚ)/10000000000),((1466507771:ℚ)/2000000000),((68316115829:ℚ)/119150000000),((1543307771:ℚ)/2364000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1555621389:ℚ)/5000000000),((-55225205730128659751725852841528678644466657318402429423:ℚ)/15858182680078125000000000000000000000000000000000000000000),((-13558609121944076719273:ℚ)/128000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((7294517931:ℚ)/10000000000),((7391928383:ℚ)/10000000000),((68850661379:ℚ)/120100000000),((7775928383:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((284489741:ℚ)/1000000000),((-1183070361241838314387653374448810093800697060527465011:ℚ)/338344453320312500000000000000000000000000000000000000000),((-14694307740302330680308259:ℚ)/138624000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((3676955791:ℚ)/5000000000),((3725658841:ℚ)/5000000000),((34692602119:ℚ)/60525000000),((3917658841:ℚ)/6005000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((637929507:ℚ)/2500000000),((-10008506264418485286002709950174272537870517141474357:ℚ)/2851334326171875000000000000000000000000000000000000000),((-3394432780215851424033:ℚ)/32000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((7413304939:ℚ)/10000000000),((7510706759:ℚ)/10000000000),((69919744451:ℚ)/122000000000),((7894706759:ℚ)/12105000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2221097841:ℚ)/10000000000),((-19990594385479404767313068798844536096051731852873506339:ℚ)/5674525000000000000000000000000000000000000000000000000000),((-4905032956700740069220833:ℚ)/46208000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7472698011:ℚ)/10000000000),((7748260939:ℚ)/10000000000),((70454282099:ℚ)/125800000000),((8132260939:ℚ)/12200000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((916439677:ℚ)/5000000000),((-4743016751011400536655941389304019993912890383188968731:ℚ)/1555363681250000000000000000000000000000000000000000000000),((-14725555939901830059268099:ℚ)/138624000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((3855133783:ℚ)/5000000000),((7985811941:ℚ)/10000000000),((36296204047:ℚ)/64800000000),((8369811941:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-97860378825365111396808740396352353698432778536421429:ℚ)/31492800000000000000000000000000000000000000000000000000),((-3404457:ℚ)/32000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7947833041:ℚ)/10000000000),((4943066361:ℚ)/5000000000),((74730497369:ℚ)/160000000000),((63395881:ℚ)/80000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-53187195954044294112124646151209:ℚ)/9600000000000000000000000000000000000),((-3404457:ℚ)/32000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((9848244843:ℚ)/10000000000),((13686509251:ℚ)/10000000000),((91834203587:ℚ)/220800000000),((14070509251:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6071474563590599212422503:ℚ)/2437632000000000000000000000),((-3404457:ℚ)/32000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((4709:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((4709:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4709:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((4709:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((4709:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound seventh nn0 nn1 Qcell ((4709:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((2421:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound seventh nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound seventh nn0 nn1 Qcell ((4709:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC26
#check @N11Formalization.C450SeventhGroupedC26.bound
#print axioms N11Formalization.C450SeventhGroupedC26.valid0
#print axioms N11Formalization.C450SeventhGroupedC26.valid1
#print axioms N11Formalization.C450SeventhGroupedC26.valid2
#print axioms N11Formalization.C450SeventhGroupedC26.valid3
#print axioms N11Formalization.C450SeventhGroupedC26.valid4
#print axioms N11Formalization.C450SeventhGroupedC26.valid5
#print axioms N11Formalization.C450SeventhGroupedC26.valid6
#print axioms N11Formalization.C450SeventhGroupedC26.valid7
#print axioms N11Formalization.C450SeventhGroupedC26.valid8
#print axioms N11Formalization.C450SeventhGroupedC26.valid9
#print axioms N11Formalization.C450SeventhGroupedC26.valid10
#print axioms N11Formalization.C450SeventhGroupedC26.valid11
#print axioms N11Formalization.C450SeventhGroupedC26.valid12
#print axioms N11Formalization.C450SeventhGroupedC26.valid13
#print axioms N11Formalization.C450SeventhGroupedC26.valid14
#print axioms N11Formalization.C450SeventhGroupedC26.valid15
#print axioms N11Formalization.C450SeventhGroupedC26.valid16
#print axioms N11Formalization.C450SeventhGroupedC26.valid17
#print axioms N11Formalization.C450SeventhGroupedC26.bound
#print axioms N11Formalization.C450SeventhGroupedC26.endpoint_checks
