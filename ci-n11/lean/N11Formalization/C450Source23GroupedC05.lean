import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3373709733:ℚ)/5000000000),((6951883787:ℚ)/10000000000),((-17495651361:ℚ)/24800000000),((-30070807063:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((478213771:ℚ)/1000000000),((545685430829402377536705180670336911430244544331885343779233:ℚ)/2706667263200000000000000000000000000000000000000000000000000),((3404836452978719936698321:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((429171091:ℚ)/625000000),((3505754971:ℚ)/5000000000),((-2945754971:ℚ)/4212500000),((-3840882001:ℚ)/6378125000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((553609103:ℚ)/1250000000),((353811538908823478664727069571870325817366542616138747:ℚ)/1799364259141921997070312500000000000000000000000000000),((26563985077986268113767:ℚ)/56406250000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((432899279:ℚ)/625000000),((1414226287:ℚ)/2000000000),((-3570678861:ℚ)/5102500000),((-3881892069:ℚ)/6437500000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((1060508473:ℚ)/2500000000),((433094428877390321962125707795227961978574130469700513597:ℚ)/2202132850509985351562500000000000000000000000000000000000),((106220403551909350056623:ℚ)/225625000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3493017173:ℚ)/5000000000),((1782687099:ℚ)/2500000000),((-4508061297:ℚ)/6437500000),((-2853017173:ℚ)/4725000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4047140089:ℚ)/10000000000),((27120010059798874670884093565950072605313546974092241547:ℚ)/137870580768585205078125000000000000000000000000000000000),((3397884709333131489211281:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((1761418811:ℚ)/2500000000),((1432111043:ℚ)/2000000000),((-402703681:ℚ)/577500000),((-15855606921:ℚ)/26106250000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3842961723:ℚ)/10000000000),((702754716307049240770767027053697626905445434676425099:ℚ)/3616082463702392578125000000000000000000000000000000000),((848863331906851446816569:ℚ)/1805000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3537746933:ℚ)/5000000000),((7190360947:ℚ)/10000000000),((-18211082841:ℚ)/26106250000),((-31875216263:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((747383317:ℚ)/2000000000),((1486536943060603126750265077411307412136357929554268092433417:ℚ)/7647940295323031711578369140625000000000000000000000000000000),((178675901340414333630059:ℚ)/380000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((7105311293:ℚ)/10000000000),((7220165607:ℚ)/10000000000),((-18300496821:ℚ)/26225000000),((-21359474741:ℚ)/35125000000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((3627926959:ℚ)/10000000000),((4325876447027403791708775300595098180577339021662637436973:ℚ)/22252517765060791015625000000000000000000000000000000000000),((13576892673517167575992161:ℚ)/28880000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7135127541:ℚ)/10000000000),((7249969209:ℚ)/10000000000),((-6129969209:ℚ)/8781250000),((-64406402951:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((351571843:ℚ)/1000000000),((921907732583469848071540568266504399344385958294808970949833:ℚ)/4741663898527574539184570312500000000000000000000000000000000),((13574385827507179479309009:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7164942627:ℚ)/10000000000),((909971471:ℚ)/1250000000),((-2309914413:ℚ)/3307812500),((-64734368897:ℚ)/106325000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3399971717:ℚ)/10000000000),((198906925807751817784515515764834690169241690659369078689569:ℚ)/1022900624022272330522537231445312500000000000000000000000000),((13571847965749496311970081:ℚ)/28880000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((1798689141:ℚ)/2500000000),((7309573297:ℚ)/10000000000),((-18568719891:ℚ)/26581250000),((-16265580551:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((32803117:ℚ)/100000000),((11301616085412822910642134318020612560907627663164505595603:ℚ)/58112056954967212677001953125000000000000000000000000000000),((848079943172382794460809:ℚ)/1805000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7224569371:ℚ)/10000000000),((7339373811:ℚ)/10000000000),((-6219373811:ℚ)/8900000000),((-65390263081:ℚ)/107275000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((789073171:ℚ)/2500000000),((61639250164760777838566861509551123956946110796269913122923:ℚ)/316903547653540039062500000000000000000000000000000000000000),((13566679203805238771590449:ℚ)/28880000000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((362719053:ℚ)/500000000),((7369173323:ℚ)/10000000000),((-18747519969:ℚ)/26818750000),((-3285909583:ℚ)/5387500000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1513689183:ℚ)/5000000000),((4254362802494349440521946704730379326773530032765247532617:ℚ)/21870071186451809108257293701171875000000000000000000000000),((33910120768828124082601:ℚ)/72200000000000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((227630989:ℚ)/312500000),((7428769393:ℚ)/10000000000),((-18926308179:ℚ)/26937500000),((-2063940879:ℚ)/3396875000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1446456847:ℚ)/5000000000),((7103433473971500013769959045303428792605599687817295672035403:ℚ)/36087016377593612670898437500000000000000000000000000000000000),((105986825504201053899727:ℚ)/225625000000000000000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((917976197:ℚ)/1250000000),((1872090403:ℚ)/2500000000),((-4776271209:ℚ)/6793750000),((-8337738167:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2603857647:ℚ)/10000000000),((12884952763983750446644480031180702362999017774303618863937:ℚ)/65452083067758846282958984375000000000000000000000000000000),((211889008188116072056601:ℚ)/451250000000000000000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((740342327:ℚ)/1000000000),((7547950079:ℚ)/10000000000),((-6427950079:ℚ)/9137500000),((-6735765597:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2279369983:ℚ)/10000000000),((65965895438618330720884063636338545199602435063605303631:ℚ)/335060755305624008178710937500000000000000000000000000000),((135553553823199093718281:ℚ)/288800000000000000000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((3731516419:ℚ)/5000000000),((7786268311:ℚ)/10000000000),((-19998804933:ℚ)/27650000000),((-3091516419:ℚ)/5200000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((15211107:ℚ)/80000000),((6936443195344910859832501981253703548051100870466803621:ℚ)/33029761132812500000000000000000000000000000000000000000),((9382579154834340319289:ℚ)/20000000000000000000000)⟩
theorem valid15 : Valid source23 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((1540286387:ℚ)/2000000000),((4369529677:ℚ)/5000000000),((-11428589031:ℚ)/14300000000),((-14127150257:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((667446424765151805570962084701992876974180984229621881:ℚ)/2588076562500000000000000000000000000000000000000000000),((233939:ℚ)/500000)⟩
theorem valid16 : Valid source23 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8654498589:ℚ)/10000000000),((1064304563:ℚ)/1000000000),((-952304563:ℚ)/1080000000),((-81119484479:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((37584185481047417762312716369354259230432687797731:ℚ)/123018750000000000000000000000000000000000000000000),((233939:ℚ)/500000)⟩
theorem valid17 : Valid source23 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((10558877971:ℚ)/10000000000),((1805964897:ℚ)/1250000000),((-4997894691:ℚ)/5000000000),((-4437724247:ℚ)/9600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3074136161680946719366513139058489:ℚ)/7812500000000000000000000000000000),((233939:ℚ)/500000)⟩
theorem valid18 : Valid source23 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source23 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((4253:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source23 nn0 nn1 Qcell ((4291:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source23 nn0 nn1 Qcell ((4253:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source23 nn0 nn1 Qcell ((4253:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC05
#check @N11Formalization.C450Source23GroupedC05.bound
#print axioms N11Formalization.C450Source23GroupedC05.valid0
#print axioms N11Formalization.C450Source23GroupedC05.valid1
#print axioms N11Formalization.C450Source23GroupedC05.valid2
#print axioms N11Formalization.C450Source23GroupedC05.valid3
#print axioms N11Formalization.C450Source23GroupedC05.valid4
#print axioms N11Formalization.C450Source23GroupedC05.valid5
#print axioms N11Formalization.C450Source23GroupedC05.valid6
#print axioms N11Formalization.C450Source23GroupedC05.valid7
#print axioms N11Formalization.C450Source23GroupedC05.valid8
#print axioms N11Formalization.C450Source23GroupedC05.valid9
#print axioms N11Formalization.C450Source23GroupedC05.valid10
#print axioms N11Formalization.C450Source23GroupedC05.valid11
#print axioms N11Formalization.C450Source23GroupedC05.valid12
#print axioms N11Formalization.C450Source23GroupedC05.valid13
#print axioms N11Formalization.C450Source23GroupedC05.valid14
#print axioms N11Formalization.C450Source23GroupedC05.valid15
#print axioms N11Formalization.C450Source23GroupedC05.valid16
#print axioms N11Formalization.C450Source23GroupedC05.valid17
#print axioms N11Formalization.C450Source23GroupedC05.valid18
#print axioms N11Formalization.C450Source23GroupedC05.bound
#print axioms N11Formalization.C450Source23GroupedC05.endpoint_checks
