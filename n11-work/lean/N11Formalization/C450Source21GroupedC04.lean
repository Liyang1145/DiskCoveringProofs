import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3374793681:ℚ)/5000000000),((6951515817:ℚ)/10000000000),((-78209705621:ℚ)/99200000000),((-8524381043:ℚ)/12637500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2387967769:ℚ)/5000000000),((711313770390130176576314887223814561883434122898993699680524981:ℚ)/6236161374412800000000000000000000000000000000000000000000000000),((6251962435810521358200228779:ℚ)/11089920000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3434361107:ℚ)/5000000000),((3505525843:ℚ)/5000000000),((-39491835959:ℚ)/50550000000),((-8703083321:ℚ)/12756250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((1105693761:ℚ)/2500000000),((76926607992044779814118401872189072081622619695591594179997:ℚ)/700629257767645019531250000000000000000000000000000000000000),((2085644572811283760867475137:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((6928284241:ℚ)/10000000000),((282823383:ℚ)/400000000),((-3190303979:ℚ)/4082000000),((-17584852723:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((2117984693:ℚ)/5000000000),((495420228527118879775673845099536269373497170363787727819:ℚ)/4509968077844450000000000000000000000000000000000000000000),((439532022171263461766633987:ℚ)/778240000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((6987842801:ℚ)/10000000000),((7130114567:ℚ)/10000000000),((-80531489371:ℚ)/103000000000),((-17763528403:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4041092619:ℚ)/10000000000),((115862053442087226016927468723523173435984103438064435720097717:ℚ)/1054247643126562500000000000000000000000000000000000000000000000),((8359621298245720631694043513:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7047397991:ℚ)/10000000000),((7159878501:ℚ)/10000000000),((-11559774359:ℚ)/14850000000),((-17942193973:ℚ)/26106250000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((1918455483:ℚ)/5000000000),((291857176067605615105321497132046096851247177467622466454703:ℚ)/2705293553486132812500000000000000000000000000000000000000000),((8362876182239165318793615753:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7077174351:ℚ)/10000000000),((7189641741:ℚ)/10000000000),((-81305342633:ℚ)/104425000000),((-18031523053:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((466356853:ℚ)/1250000000),((211291755888578535587082854915298762118814860162884291030041817:ℚ)/1957872715602696118164062500000000000000000000000000000000000000),((25101352983453095478144968939:ℚ)/44359680000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((7106949903:ℚ)/10000000000),((1443880859:ℚ)/2000000000),((-16338451167:ℚ)/20980000000),((-18120849709:ℚ)/26343750000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((1810923361:ℚ)/5000000000),((44277989499584664354585366013682522524136324695021653600023:ℚ)/410158407445600500000000000000000000000000000000000000000000),((25114064500101597224820255851:ℚ)/44359680000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7136724657:ℚ)/10000000000),((3617142659:ℚ)/5000000000),((-13647618189:ℚ)/17562500000),((-18210173971:ℚ)/26403125000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((3509611059:ℚ)/10000000000),((543139544148503580747725567541871214574225383614194674876211:ℚ)/5077415407958602905273437500000000000000000000000000000000000),((25118902375683615950013631211:ℚ)/44359680000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7151611739:ℚ)/10000000000),((7249166173:ℚ)/10000000000),((-4828185897:ℚ)/6212500000),((-18254835217:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1726092347:ℚ)/5000000000),((3539751878113172787419895638675138113728606483756720040331:ℚ)/33084524764392089843750000000000000000000000000000000000000),((8375082307661846907995828273:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((57331989:ℚ)/80000000),((7264046861:ℚ)/10000000000),((-82272609193:ℚ)/105850000000),((-146395967:ℚ)/212175000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((678765413:ℚ)/2000000000),((6348111814947158145786573692870942223395016689210239291977091337:ℚ)/59322370824313853906250000000000000000000000000000000000000000000),((1608421647530710605162419:ℚ)/2839019520000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7181385317:ℚ)/10000000000),((909865923:ℚ)/1250000000),((-10308256999:ℚ)/13260937500),((-18344155951:ℚ)/26581250000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3334489203:ℚ)/10000000000),((76466336319257475012953445237302371980905839983682271548811:ℚ)/714442203380918097496032714843750000000000000000000000000000),((8379308778568525853272628657:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((7196271817:ℚ)/10000000000),((114198249:ℚ)/156250000),((-1294577237:ℚ)/1661328125),((-18388815451:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((409264717:ℚ)/1250000000),((28255736672428533995931886142644593399338593923043675237931:ℚ)/261504256297352457046508789062500000000000000000000000000000),((8384040526374149648995111657:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7226044243:ℚ)/10000000000),((45865299:ℚ)/62500000),((-520248887:ℚ)/667500000),((-2639733247:ℚ)/3831250000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((393754373:ℚ)/1250000000),((393191880356964053985338624828577549482645882065651261:ℚ)/3637923378675842285156250000000000000000000000000000000),((8388260488134043467745103937:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((3627907957:ℚ)/5000000000),((7368207103:ℚ)/10000000000),((-83626692339:ℚ)/107275000000),((-9283723871:ℚ)/13468750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3021039339:ℚ)/10000000000),((605286071867524830533463515750151052367380787802605495793651:ℚ)/5598738223731663131713867187500000000000000000000000000000000),((2098119037744824753122784337:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((182139671:ℚ)/250000000),((7397965733:ℚ)/10000000000),((-84013554529:ℚ)/107750000000),((-466419013:ℚ)/676406250),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((2886471559:ℚ)/10000000000),((990315453858813706096477380723307012888628918536772605115807249:ℚ)/9157713296635931396484375000000000000000000000000000000000000000),((5247929697682998685505833:ℚ)/9241600000000000000000000)⟩
theorem valid14 : Valid source21 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7315357031:ℚ)/10000000000),((371386187:ℚ)/500000000),((-468891159:ℚ)/601250000),((-18746071093:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((343188969:ℚ)/1250000000),((4692472002079963186450999598559284566803382499199875547:ℚ)/43381308719689941406250000000000000000000000000000000000),((8400894585803917845051917193:ℚ)/14786560000000000000000000000)⟩
theorem valid15 : Valid source21 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source21 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1469025299:ℚ)/2000000000),((1497447583:ℚ)/2000000000),((-17034818579:ℚ)/21740000000),((-3767075897:ℚ)/5482500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((259711863:ℚ)/1000000000),((944848340001785186856418428306808338741320596450140410670211:ℚ)/8578935431857287500000000000000000000000000000000000000000000),((17705972584385455511809627:ℚ)/31129600000000000000000000)⟩
theorem valid16 : Valid source21 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((3702331643:ℚ)/5000000000),((754674969:ℚ)/1000000000),((-199878479:ℚ)/255000000),((-9506994929:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((227213823:ℚ)/1000000000),((7793224301926190578686698265446933423149935546398113:ℚ)/70741262658691406250000000000000000000000000000000000),((2104682359881836872399857137:ℚ)/3696640000000000000000000000)⟩
theorem valid17 : Valid source21 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((3732098643:ℚ)/5000000000),((3892387:ℚ)/5000000),((-44521031:ℚ)/55300000),((-872390539:ℚ)/1300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((236658039:ℚ)/1250000000),((1668779658300312172513739840985556610581876098787:ℚ)/13740380631250000000000000000000000000000000000000),((6319501971796323427810889411:ℚ)/11089920000000000000000000000)⟩
theorem valid18 : Valid source21 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((7702306777:ℚ)/10000000000),((8736562931:ℚ)/10000000000),((-9219574373:ℚ)/10400000000),((-19906920331:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((628302897366105324496656499838252676402232348677600804079:ℚ)/3843871200000000000000000000000000000000000000000000000000),((583181579:ℚ)/1024000000)⟩
theorem valid19 : Valid source21 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((8654386183:ℚ)/10000000000),((10639119083:ℚ)/10000000000),((-126148548079:ℚ)/129600000000),((-22763158549:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((175873652276370122943579399534298481511878658092961031751:ℚ)/850305600000000000000000000000000000000000000000000000000),((583181579:ℚ)/1024000000)⟩
theorem valid20 : Valid source21 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((2111471401:ℚ)/2000000000),((3610529329:ℚ)/2500000000),(-1:ℚ),((-5694414203:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((14561962536052547213993947:ℚ)/60940800000000000000000000),((583181579:ℚ)/1024000000)⟩
theorem valid21 : Valid source21 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((4177:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source21 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((4177:ℚ)/6400) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8449:ℚ)/12800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8449:ℚ)/12800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source21 nn0 nn1 Qcell ((8449:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((4253:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((4253:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source21 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source21 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source21 nn0 nn1 Qcell ((4253:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source21 nn0 nn1 Qcell ((4253:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC04
#check @N11Formalization.C450Source21GroupedC04.bound
#print axioms N11Formalization.C450Source21GroupedC04.valid0
#print axioms N11Formalization.C450Source21GroupedC04.valid1
#print axioms N11Formalization.C450Source21GroupedC04.valid2
#print axioms N11Formalization.C450Source21GroupedC04.valid3
#print axioms N11Formalization.C450Source21GroupedC04.valid4
#print axioms N11Formalization.C450Source21GroupedC04.valid5
#print axioms N11Formalization.C450Source21GroupedC04.valid6
#print axioms N11Formalization.C450Source21GroupedC04.valid7
#print axioms N11Formalization.C450Source21GroupedC04.valid8
#print axioms N11Formalization.C450Source21GroupedC04.valid9
#print axioms N11Formalization.C450Source21GroupedC04.valid10
#print axioms N11Formalization.C450Source21GroupedC04.valid11
#print axioms N11Formalization.C450Source21GroupedC04.valid12
#print axioms N11Formalization.C450Source21GroupedC04.valid13
#print axioms N11Formalization.C450Source21GroupedC04.valid14
#print axioms N11Formalization.C450Source21GroupedC04.valid15
#print axioms N11Formalization.C450Source21GroupedC04.valid16
#print axioms N11Formalization.C450Source21GroupedC04.valid17
#print axioms N11Formalization.C450Source21GroupedC04.valid18
#print axioms N11Formalization.C450Source21GroupedC04.valid19
#print axioms N11Formalization.C450Source21GroupedC04.valid20
#print axioms N11Formalization.C450Source21GroupedC04.valid21
#print axioms N11Formalization.C450Source21GroupedC04.bound
#print axioms N11Formalization.C450Source21GroupedC04.endpoint_checks
