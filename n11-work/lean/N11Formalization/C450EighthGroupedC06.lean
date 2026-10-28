import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((3173584353:ℚ)/5000000000),((1656697009:ℚ)/2500000000),((-17263667099:ℚ)/24800000000),((-2949584353:ℚ)/5150000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1455960037:ℚ)/2500000000),((50286192487747077657849405957797987472786028965812743892551:ℚ)/3034106102400000000000000000000000000000000000000000000000000),((3281459485613916073118849:ℚ)/23104000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((3292386603:ℚ)/5000000000),((3432201187:ℚ)/5000000000),((-35834213057:ℚ)/51500000000),((-3068386603:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2614069979:ℚ)/5000000000),((251675114000810131415213008595303197187352959727085389624919:ℚ)/15214729512304687500000000000000000000000000000000000000000000),((13133673054205685937402601:ℚ)/92416000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((3411185133:ℚ)/5000000000),((6983206543:ℚ)/10000000000),((-72975271973:ℚ)/106800000000),((-3187185133:ℚ)/5435000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2281598383:ℚ)/5000000000),((47428259823948432283800014601072653517266678747237705375502377:ℚ)/2998690258899600000000000000000000000000000000000000000000000000),((52541279364233283500757121:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((5552933:ℚ)/8000000),((3521303961:ℚ)/5000000000),((-36814343571:ℚ)/54350000000),((-1731511:ℚ)/2924000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4194542279:ℚ)/10000000000),((2074244446546925817721051709663481272880092286636392387252997:ℚ)/134045866122770117187500000000000000000000000000000000000000000),((39408555678910314375435827:ℚ)/277248000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7000563643:ℚ)/10000000000),((7102008849:ℚ)/10000000000),((-24760699113:ℚ)/36550000000),((-6552563643:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((249894371:ℚ)/625000000),((22570199608493997632977961661006119800882406214516479383639:ℚ)/1458184407090075683593750000000000000000000000000000000000000),((157659574312132320822565187:ℚ)/1108992000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((1764990163:ℚ)/2500000000),((3565854573:ℚ)/5000000000),((-37304400303:ℚ)/55300000000),((-550996721:ℚ)/925625000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((758502019:ℚ)/2000000000),((8875294537379821712108477959997919443572470975053431466943169:ℚ)/579569519264214062500000000000000000000000000000000000000000000),((39416265110953659061700123:ℚ)/277248000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1417931803:ℚ)/2000000000),((3580704667:ℚ)/5000000000),((-37467751337:ℚ)/55537500000),((-1328331803:ℚ)/2231000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((921380811:ℚ)/2500000000),((5101233059468128388706894667358246482508809830595862781089359:ℚ)/333056684165447866058349609375000000000000000000000000000000000),((13139828835216597722588281:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3559678643:ℚ)/5000000000),((3595554707:ℚ)/5000000000),((-37631101777:ℚ)/55775000000),((-3335678643:ℚ)/5601250000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3575487093:ℚ)/10000000000),((13342680674953983358953169131684768123568142446007334914248599:ℚ)/870980904065008402343750000000000000000000000000000000000000000),((13140909625268860996762121:ℚ)/92416000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((1429811093:ℚ)/2000000000),((1805202347:ℚ)/2500000000),((-18897225817:ℚ)/28006250000),((-446737031:ℚ)/750000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3462110407:ℚ)/10000000000),((295812863924920112516408844841523639254223783079297551:ℚ)/19306672806000709533691406250000000000000000000000000000),((3285499351794890373086361:ℚ)/23104000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3589376777:ℚ)/5000000000),((906313657:ℚ)/1250000000),((-9489450227:ℚ)/14062500000),((-3365376777:ℚ)/5648750000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1672526503:ℚ)/5000000000),((1813065872744115572607890678436027194833848902920165464701503:ℚ)/118312614512443542480468750000000000000000000000000000000000000),((821443261302046133638321:ℚ)/5776000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3604225777:ℚ)/5000000000),((3640104511:ℚ)/5000000000),((-38121149621:ℚ)/56487500000),((-3380225777:ℚ)/5672500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3223913449:ℚ)/10000000000),((222228274346436612724151820948796771600502365641396823118283:ℚ)/14499268117040759246826171875000000000000000000000000000000000),((13144193946363919555007009:ℚ)/92416000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3619074733:ℚ)/5000000000),((1461981737:ℚ)/2000000000),((-15313799107:ℚ)/22690000000),((-3395074733:ℚ)/5696250000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((154910619:ℚ)/500000000),((23241455515148821574788535018975431402055128515311053484704741:ℚ)/1516147877097750881250000000000000000000000000000000000000000000),((2103248432579603673220401:ℚ)/14786560000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((7267847291:ℚ)/10000000000),((3669804123:ℚ)/5000000000),((-12815948451:ℚ)/18987500000),((-6819847291:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((2967369587:ℚ)/10000000000),((33284233209781247654939561458419740062045322136476973151:ℚ)/2170952927209472656250000000000000000000000000000000000000),((39439255357720340737151723:ℚ)/277248000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7297545031:ℚ)/10000000000),((231218971:ℚ)/312500000),((-2423408681:ℚ)/3575000000),((-2283181677:ℚ)/3845000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2830671551:ℚ)/10000000000),((306640794259993352948262843607655832829234872764743549:ℚ)/19789832791065216064453125000000000000000000000000000000),((25682188546924363738507:ℚ)/180500000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((229904383:ℚ)/312500000),((1864601377:ℚ)/2500000000),((-19550615147:ℚ)/28837500000),((-215904383:ℚ)/363437500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((507176373:ℚ)/2000000000),((1047249294517274912454062079168468393274596245812261475391527:ℚ)/67575771812825793457031250000000000000000000000000000000000000),((3287890243126029140630241:ℚ)/23104000000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7416335151:ℚ)/10000000000),((7577201249:ℚ)/10000000000),((-79509213739:ℚ)/116300000000),((-6968335151:ℚ)/11820000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((137682821:ℚ)/625000000),((1508332276949828930892481473274857884161501653068596263522397:ℚ)/95387534255192187500000000000000000000000000000000000000000000),((52629699802921940054322529:ℚ)/369664000000000000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((7535123981:ℚ)/10000000000),((1562957691:ℚ)/2000000000),((-5474844867:ℚ)/7880000000),((-7087123981:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1307554269:ℚ)/10000000000),((186800777114986667293623937437006063982992331518520930821:ℚ)/11379373173200000000000000000000000000000000000000000000000),((34621996637670361:ℚ)/243200000000000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7772698011:ℚ)/10000000000),((8289947517:ℚ)/10000000000),((-87349422687:ℚ)/122000000000),((-7324698011:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1305001035110478144173927584068570205424863458035593828957081:ℚ)/74461117050000000000000000000000000000000000000000000000000000),((18220259:ℚ)/128000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8247833041:ℚ)/10000000000),((10190432601:ℚ)/10000000000),((-36084919537:ℚ)/43200000000),((-7799833041:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((35559420683923012945620439708216219539970100109056440253:ℚ)/1511654400000000000000000000000000000000000000000000000000),((18220259:ℚ)/128000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((10148244843:ℚ)/10000000000),((13991001959:ℚ)/10000000000),((-150061021549:ℚ)/160000000000),((-9700244843:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((144464580978177708171210996756402946811809:ℚ)/4875264000000000000000000000000000000000000),((18220259:ℚ)/128000000)⟩
theorem valid19 : Valid eighth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet19 valid19
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
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC06
#check @N11Formalization.C450EighthGroupedC06.bound
#print axioms N11Formalization.C450EighthGroupedC06.valid0
#print axioms N11Formalization.C450EighthGroupedC06.valid1
#print axioms N11Formalization.C450EighthGroupedC06.valid2
#print axioms N11Formalization.C450EighthGroupedC06.valid3
#print axioms N11Formalization.C450EighthGroupedC06.valid4
#print axioms N11Formalization.C450EighthGroupedC06.valid5
#print axioms N11Formalization.C450EighthGroupedC06.valid6
#print axioms N11Formalization.C450EighthGroupedC06.valid7
#print axioms N11Formalization.C450EighthGroupedC06.valid8
#print axioms N11Formalization.C450EighthGroupedC06.valid9
#print axioms N11Formalization.C450EighthGroupedC06.valid10
#print axioms N11Formalization.C450EighthGroupedC06.valid11
#print axioms N11Formalization.C450EighthGroupedC06.valid12
#print axioms N11Formalization.C450EighthGroupedC06.valid13
#print axioms N11Formalization.C450EighthGroupedC06.valid14
#print axioms N11Formalization.C450EighthGroupedC06.valid15
#print axioms N11Formalization.C450EighthGroupedC06.valid16
#print axioms N11Formalization.C450EighthGroupedC06.valid17
#print axioms N11Formalization.C450EighthGroupedC06.valid18
#print axioms N11Formalization.C450EighthGroupedC06.valid19
#print axioms N11Formalization.C450EighthGroupedC06.bound
#print axioms N11Formalization.C450EighthGroupedC06.endpoint_checks
