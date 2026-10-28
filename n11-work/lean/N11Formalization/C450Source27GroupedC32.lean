import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((15:ℚ)/16),(1:ℚ),((2579999999:ℚ)/5000000000),((2745293891:ℚ)/5000000000),((9339999997:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2061170957:ℚ)/2500000000),((-3178488145920655036801032459464363070191261088767390811:ℚ)/6829543750000000000000000000000000000000000000000000000),((-270550604441050169482099427:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2698749999:ℚ)/5000000000),((2864211569:ℚ)/5000000000),((9696249997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7810178059:ℚ)/10000000000),((-295185400587160660984758871747819402827317915097855497:ℚ)/634472100000000000000000000000000000000000000000000000),((-262454192391380185469599427:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2817499999:ℚ)/5000000000),((2923666003:ℚ)/5000000000),((10052499997:ℚ)/10870000000),(1:ℚ),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3677857677:ℚ)/5000000000),((-3909832263750900479876129653431537680429638911715629491:ℚ)/8027284393750000000000000000000000000000000000000000000),((-259123559975768581257099427:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2876874999:ℚ)/5000000000),((5906784371:ℚ)/10000000000),((10230624997:ℚ)/10965000000),(1:ℚ),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((7119760073:ℚ)/10000000000),((-341802307031328208774732628259950419193222943344825657:ℚ)/686633011523437500000000000000000000000000000000000000),((-257480529550359017175849427:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2906562499:ℚ)/5000000000),((1491558851:ℚ)/2500000000),((1474241071:ℚ)/1580000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3499668727:ℚ)/5000000000),((-191596268331220478277837849594271791719246166922353:ℚ)/385186718750000000000000000000000000000000000000000),((-255488190990021704241474427:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2936249999:ℚ)/5000000000),((301284257:ℚ)/500000000),((107306701:ℚ)/115000000),(1:ℚ),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((171929191:ℚ)/250000000),((-295289717907889936022099916241358227300715560003:ℚ)/594091796875000000000000000000000000000000000000),((-253499604409174358444599427:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((2965937499:ℚ)/5000000000),((1513852383:ℚ)/2500000000),((10497812497:ℚ)/11202500000),(1:ℚ),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((6753153227:ℚ)/10000000000),((-176524987228910399601540934473755121124489498145457719:ℚ)/351467252503906250000000000000000000000000000000000000),((-252691112331773510985224427:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((2980781249:ℚ)/5000000000),((1521283403:ℚ)/2500000000),((10542343747:ℚ)/11250000000),(1:ℚ),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3345210747:ℚ)/5000000000),((-5817289107348046612659012244303299976715737916324807:ℚ)/11587142944335937500000000000000000000000000000000000),((-251700088295669479332099427:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((2995624999:ℚ)/5000000000),((6114857383:ℚ)/10000000000),((10586874997:ℚ)/11297500000),(1:ℚ),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((331359403:ℚ)/500000000),((-4522700740743372065770493612164738519300407814691061979:ℚ)/9012122105371093750000000000000000000000000000000000000),((-250710001650912333063349427:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3010468749:ℚ)/5000000000),((6144580851:ℚ)/10000000000),((10631406247:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((65634381:ℚ)/100000000),((-11445487852510772649242491538013626944761389403476969:ℚ)/22815685759765625000000000000000000000000000000000000),((-249720852160049374578974427:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3025312499:ℚ)/5000000000),((6174304017:ℚ)/10000000000),((10675937497:ℚ)/11392500000),(1:ℚ),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((649915609:ℚ)/1000000000),((-1544721193574917398116439767500058034725763540035955413:ℚ)/3080462131933593750000000000000000000000000000000000000),((-248732639783505154278974427:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3040156249:ℚ)/5000000000),((775503361:ℚ)/1250000000),((10720468747:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1608581439:ℚ)/2500000000),((-4690608409856276784612261226864982154901427740332940541:ℚ)/9357462400000000000000000000000000000000000000000000000),((-247745364244251524963349427:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((9171:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3054999999:ℚ)/5000000000),((1554722053:ℚ)/2500000000),((10764999997:ℚ)/11463750000),(1:ℚ),((9553242939:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((600082529:ℚ)/2000000000),((6368930027:ℚ)/10000000000),((-1581232530184904697270291890250304065322061271089232617:ℚ)/3138621041711425781250000000000000000000000000000000000),((-247347166271807385832099427:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((9171:ℚ)/12800) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((9171:ℚ)/12800),((919:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((1531210937:ℚ)/2500000000),((1246749893:ℚ)/2000000000),((5393632811:ℚ)/5743750000),(1:ℚ),((9548320353:ℚ)/10000000000),((149269421:ℚ)/156250000),((1508511599:ℚ)/5000000000),((1584003643:ℚ)/2500000000),((-596538146529448565177123132337405189640233704181897813:ℚ)/1184313291931152343750000000000000000000000000000000000),((-61713586310479115571403763:ℚ)/184832000000000000000000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((9171:ℚ)/12800) ((919:ℚ)/1280) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((919:ℚ)/1280),((9209:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3069843749:ℚ)/5000000000),((1562152661:ℚ)/2500000000),((10809531247:ℚ)/11511250000),(1:ℚ),((74558193:ℚ)/78125000),((4774160179:ℚ)/5000000000),((1516687521:ℚ)/5000000000),((252118039:ℚ)/400000000),((-293031816534677359301643305516625457204444548762969:ℚ)/581872102863341569900512695312500000000000000000000),((-246361758431242048885224427:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell ((919:ℚ)/1280) ((9209:ℚ)/12800) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((9209:ℚ)/12800),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((384658203:ℚ)/625000000),((782933969:ℚ)/1250000000),((1353974609:ℚ)/1441875000),(1:ℚ),((59616423:ℚ)/62500000),((9543448709:ℚ)/10000000000),((762368323:ℚ)/2500000000),((125394737:ℚ)/200000000),((-122830256561835490122088821545036933732294940109:ℚ)/243950455248355865478515625000000000000000000000),((-3841709464391528075483243:ℚ)/11552000000000000000000000)⟩
theorem valid15 : Valid source27 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source27 nn0 nn1 Qcell ((9209:ℚ)/12800) ((2307:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2307:ℚ)/3200),((9247:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3084687499:ℚ)/5000000000),((6278332789:ℚ)/10000000000),((10854062497:ℚ)/11558750000),(1:ℚ),((4766928483:ℚ)/5000000000),((1907725537:ℚ)/2000000000),((3065322907:ℚ)/10000000000),((779546219:ℚ)/1250000000),((-1214713067675640992183427383643963776374843499420458959:ℚ)/2412973975289916992187500000000000000000000000000000000),((-245377287111363706122724427:ℚ)/739328000000000000000000000)⟩
theorem valid16 : Valid source27 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source27 nn0 nn1 Qcell ((2307:ℚ)/3200) ((9247:ℚ)/12800) :=
  cell_of_packet source27 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((9247:ℚ)/12800),((4633:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1546054687:ℚ)/2500000000),((3146596877:ℚ)/5000000000),((5438164061:ℚ)/5791250000),(1:ℚ),((1905827251:ℚ)/2000000000),((9533856971:ℚ)/10000000000),((3080928657:ℚ)/10000000000),((6202847171:ℚ)/10000000000),((-24439718708683117080352236926042506281175625962461707:ℚ)/48557570379394531250000000000000000000000000000000000),((-61221350660433806590153763:ℚ)/184832000000000000000000000)⟩
theorem valid17 : Valid source27 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source27 nn0 nn1 Qcell ((9247:ℚ)/12800) ((4633:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4633:ℚ)/6400),((1857:ℚ)/2560),((15:ℚ)/16),(1:ℚ),((3099531249:ℚ)/5000000000),((6308054649:ℚ)/10000000000),((10898593747:ℚ)/11606250000),(1:ℚ),((9524465239:ℚ)/10000000000),((476456813:ℚ)/500000000),((3096295161:ℚ)/10000000000),((6169166531:ℚ)/10000000000),((-1639052308646391602670766445479565826296346431001185167:ℚ)/3257125749206542968750000000000000000000000000000000000),((-244393752233021458344599427:ℚ)/739328000000000000000000000)⟩
theorem valid18 : Valid source27 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source27 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1857:ℚ)/2560) :=
  cell_of_packet source27 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((1857:ℚ)/2560),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((776738281:ℚ)/1250000000),((3161457737:ℚ)/5000000000),((2730214843:ℚ)/2907500000),(1:ℚ),((9519843613:ℚ)/10000000000),((2381116311:ℚ)/2500000000),((622285377:ℚ)/2000000000),((3067662593:ℚ)/5000000000),((-77288939376404512547935026547591896209462787267065101:ℚ)/153616967480468750000000000000000000000000000000000000),((-15243895992826400129667347:ℚ)/46208000000000000000000000)⟩
theorem valid19 : Valid source27 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source27 nn0 nn1 Qcell ((1857:ℚ)/2560) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1163:ℚ)/1600),((9323:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3114374999:ℚ)/5000000000),((6337776229:ℚ)/10000000000),((10943124997:ℚ)/11653750000),(1:ℚ),((2378817769:ℚ)/2500000000),((4759921809:ℚ)/5000000000),((156316407:ℚ)/500000000),((3050660211:ℚ)/5000000000),((-310996851345649955942787207998117990361932626968631691:ℚ)/618240036977386474609375000000000000000000000000000000),((-243411153598338057550849427:ℚ)/739328000000000000000000000)⟩
theorem valid20 : Valid source27 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((9323:ℚ)/12800) :=
  cell_of_packet source27 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((9323:ℚ)/12800),((4671:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1560898437:ℚ)/2500000000),((3176318457:ℚ)/5000000000),((5482695311:ℚ)/5838750000),(1:ℚ),((148605427:ℚ)/156250000),((9515271081:ℚ)/10000000000),((98156347:ℚ)/312500000),((758393681:ℚ)/1250000000),((-16972960502134640799025580153313587559379275889817:ℚ)/33747157689929008483886718750000000000000000000000),((-60730051343092106193278763:ℚ)/184832000000000000000000000)⟩
theorem valid21 : Valid source27 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source27 nn0 nn1 Qcell ((9323:ℚ)/12800) ((4671:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((4671:ℚ)/6400),((9361:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3129218749:ℚ)/5000000000),((6367497531:ℚ)/10000000000),((10987656247:ℚ)/11701250000),(1:ℚ),((1188284009:ℚ)/1250000000),((9510747333:ℚ)/10000000000),((157772791:ℚ)/500000000),((6032809399:ℚ)/10000000000),((-78675511500686992222763481700593144911350540301411761:ℚ)/156457655502510070800781250000000000000000000000000000),((-242429491128162604541474427:ℚ)/739328000000000000000000000)⟩
theorem valid22 : Valid source27 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source27 nn0 nn1 Qcell ((4671:ℚ)/6400) ((9361:ℚ)/12800) :=
  cell_of_packet source27 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((9361:ℚ)/12800),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((196040039:ℚ)/312500000),((6382358079:ℚ)/10000000000),((688120117:ℚ)/732812500),(1:ℚ),((9501845013:ℚ)/10000000000),((9506272077:ℚ)/10000000000),((792422551:ℚ)/2500000000),((374893583:ℚ)/625000000),((-1236586656438822287879630026872454676452180973631759:ℚ)/2459566807746887207031250000000000000000000000000000),((-945074261348812681468467:ℚ)/2888000000000000000000000)⟩
theorem valid23 : Valid source27 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source27 nn0 nn1 Qcell ((9361:ℚ)/12800) ((469:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((469:ℚ)/640),((9399:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3144062499:ℚ)/5000000000),((4997827:ℚ)/7812500),((11032187497:ℚ)/11748750000),(1:ℚ),((474873293:ℚ)/500000000),((4750922509:ℚ)/5000000000),((636742009:ℚ)/2000000000),((5963610207:ℚ)/10000000000),((-17617595616568276946448515190023342805299677155053:ℚ)/35047473541259765625000000000000000000000000000000),((-241448764624617851316474427:ℚ)/739328000000000000000000000)⟩
theorem valid24 : Valid source27 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source27 nn0 nn1 Qcell ((469:ℚ)/640) ((9399:ℚ)/12800) :=
  cell_of_packet source27 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((9399:ℚ)/12800),((4709:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1575742187:ℚ)/2500000000),((1603019743:ℚ)/2500000000),((5527226561:ℚ)/5886250000),(1:ℚ),((9493134321:ℚ)/10000000000),((1899493173:ℚ)/2000000000),((1598759513:ℚ)/5000000000),((5928744921:ℚ)/10000000000),((-37684427623556926165364412874466606740950242830495911:ℚ)/74980305627441406250000000000000000000000000000000000),((-60239688091319729580778763:ℚ)/184832000000000000000000000)⟩
theorem valid25 : Valid source27 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source27 nn0 nn1 Qcell ((9399:ℚ)/12800) ((4709:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((4709:ℚ)/6400),((9437:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3158906249:ℚ)/5000000000),((3213469659:ℚ)/5000000000),((11076718747:ℚ)/11796250000),(1:ℚ),((948885011:ℚ)/1000000000),((4746567163:ℚ)/5000000000),((802780177:ℚ)/2500000000),((2946849133:ℚ)/5000000000),((-51552797573837906927534622237931472830511470433863501:ℚ)/102591627984985351562500000000000000000000000000000000),((-240468974008552898675849427:ℚ)/739328000000000000000000000)⟩
theorem valid26 : Valid source27 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source27 nn0 nn1 Qcell ((4709:ℚ)/6400) ((9437:ℚ)/12800) :=
  cell_of_packet source27 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((9437:ℚ)/12800),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((791582031:ℚ)/1250000000),((6441799597:ℚ)/10000000000),((2774746093:ℚ)/2955000000),(1:ℚ),((4742306471:ℚ)/5000000000),((1897770023:ℚ)/2000000000),((806129637:ℚ)/2500000000),((5858466943:ℚ)/10000000000),((-6752085616161283431055837961679373252353488611772113:ℚ)/13439132226562500000000000000000000000000000000000000),((-14998714349625952623417347:ℚ)/46208000000000000000000000)⟩
theorem valid27 : Valid source27 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source27 nn0 nn1 Qcell ((9437:ℚ)/12800) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3173749999:ℚ)/5000000000),((1294303991:ℚ)/2000000000),((11121249997:ℚ)/11867500000),(1:ℚ),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((5823047559:ℚ)/10000000000),((-5220439315320779852528320357473994955516815989733871731:ℚ)/10446185617480468750000000000000000000000000000000000000),((-238902022162594306619599427:ℚ)/739328000000000000000000000)⟩
theorem valid28 : Valid source27 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3188593749:ℚ)/5000000000),((6501240051:ℚ)/10000000000),((11165781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((2875815259:ℚ)/5000000000),((-5281778254356685608204690360084213330983627802021047289:ℚ)/10572121786718750000000000000000000000000000000000000000),((-237924108070542907147724427:ℚ)/739328000000000000000000000)⟩
theorem valid29 : Valid source27 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source27 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3203437499:ℚ)/5000000000),((408184993:ℚ)/625000000),((11210312497:ℚ)/11962500000),(1:ℚ),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((1135883577:ℚ)/2000000000),((-113997220757423375022672038866203517650804689392493:ℚ)/228246742968750000000000000000000000000000000000000),((-236947129391065913060224427:ℚ)/739328000000000000000000000)⟩
theorem valid30 : Valid source27 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source27 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source27 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3218281249:ℚ)/5000000000),((6560679469:ℚ)/10000000000),((11254843747:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((5606378567:ℚ)/10000000000),((-1351491531148835725571373075444095370816851677700638101:ℚ)/2706755626562500000000000000000000000000000000000000000),((-235971086005436975557099427:ℚ)/739328000000000000000000000)⟩
theorem valid31 : Valid source27 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source27 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨((1201:ℚ)/1600),((4823:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3233124999:ℚ)/5000000000),((6590398797:ℚ)/10000000000),((11299374997:ℚ)/12057500000),(1:ℚ),((9444767421:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1673989387:ℚ)/5000000000),((1383119867:ℚ)/2500000000),((-781259980929634619253012969746148334108854790365818853:ℚ)/1565142156347656250000000000000000000000000000000000000),((-234995977794929745838349427:ℚ)/739328000000000000000000000)⟩
theorem valid32 : Valid source27 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((4823:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet32 valid32
def packet33 : Packet := ⟨((4823:ℚ)/6400),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3247968749:ℚ)/5000000000),((3310058937:ℚ)/5000000000),((11343906247:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((4722383713:ℚ)/5000000000),((674104879:ℚ)/2000000000),((1364421327:ℚ)/2500000000),((-461015280041105264861256678460113314911479151828497467:ℚ)/923832321679687500000000000000000000000000000000000000),((-234021804680393324703974427:ℚ)/739328000000000000000000000)⟩
theorem valid33 : Valid source27 packet33 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf33 :
    CellBound source27 nn0 nn1 Qcell ((4823:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet33 valid33
def packet34 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3262812499:ℚ)/5000000000),((667955529:ℚ)/1000000000),((11388437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((538195841:ℚ)/1000000000),((-5605721558315374746584610142697004222027905587023857631:ℚ)/11349050000000000000000000000000000000000000000000000000),((-231872440101099648153974427:ℚ)/739328000000000000000000000)⟩
theorem valid34 : Valid source27 packet34 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf34 :
    CellBound source27 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet34 valid34
def packet35 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3292499999:ℚ)/5000000000),((336949587:ℚ)/500000000),((11477499997:ℚ)/12295000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((5227542293:ℚ)/10000000000),((-358456381394819320762310682645816607587185907870974179:ℚ)/726015067333984375000000000000000000000000000000000000),((-229928787121257719207099427:ℚ)/739328000000000000000000000)⟩
theorem valid35 : Valid source27 packet35 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf35 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet35 valid35
def packet36 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3322187499:ℚ)/5000000000),((3399213623:ℚ)/5000000000),((1652366071:ℚ)/1770000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((1013774429:ℚ)/2000000000),((-5701614690865570643348057721841792945773984494116051:ℚ)/11552568750000000000000000000000000000000000000000000),((-227988872150772048597724427:ℚ)/739328000000000000000000000)⟩
theorem valid36 : Valid source27 packet36 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf36 :
    CellBound source27 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet36 valid36
def packet37 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3351874999:ℚ)/5000000000),((864661939:ℚ)/1250000000),((11655624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4905532113:ℚ)/10000000000),((-1505461940335859407616057143547785675700155754232053019:ℚ)/3110727362500000000000000000000000000000000000000000000),((-223700579632449317925849427:ℚ)/739328000000000000000000000)⟩
theorem valid37 : Valid source27 packet37 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf37 :
    CellBound source27 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet37 valid37
def packet38 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3411249999:ℚ)/5000000000),((7155021627:ℚ)/10000000000),((11833749997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2281404683:ℚ)/5000000000),((-234875538093800756085447090629230368357636137274793673:ℚ)/503884800000000000000000000000000000000000000000000000),((-215135508803657847594599427:ℚ)/739328000000000000000000000)⟩
theorem valid38 : Valid source27 packet38 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf38 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet38 valid38
def packet39 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3529999999:ℚ)/5000000000),((7630436233:ℚ)/10000000000),((1741428571:ℚ)/1960000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((237023141:ℚ)/625000000),((-799526321121599358186093749443077776878630327813:ℚ)/1838265625000000000000000000000000000000000000000),((-199255791539478045382099427:ℚ)/739328000000000000000000000)⟩
theorem valid39 : Valid source27 packet39 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf39 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet39 valid39
def packet40 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3767499999:ℚ)/5000000000),((1621161453:ℚ)/2000000000),((12902499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),((10470439:ℚ)/80000000),((-8307336978284332812231331728449025399410361859313365771:ℚ)/18975171200000000000000000000000000000000000000000000000),((-202894426564949567557099427:ℚ)/739328000000000000000000000)⟩
theorem valid40 : Valid source27 packet40 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf40 :
    CellBound source27 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet40 valid40
def packet41 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((4004999999:ℚ)/5000000000),((9056443481:ℚ)/10000000000),((13614999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-2498368555024565275765897335426500397102857941052388531:ℚ)/6400000000000000000000000000000000000000000000000000000),((-56346473:ℚ)/204800000)⟩
theorem valid41 : Valid source27 packet41 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf41 :
    CellBound source27 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet41 valid41
def packet42 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4479999999:ℚ)/5000000000),((257162237:ℚ)/200000000),((15039999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-185832354077531845901811732639388531:ℚ)/897048576000000000000000000000000000),((-56346473:ℚ)/204800000)⟩
theorem valid42 : Valid source27 packet42 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf42 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet42 valid42
private theorem node0_2 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source27 nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source27 nn0 nn1 Qcell ((9171:ℚ)/12800) ((9209:ℚ)/12800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((9209:ℚ)/12800) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source27 nn0 nn1 Qcell ((2269:ℚ)/3200) ((9209:ℚ)/12800) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source27 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source27 nn0 nn1 Qcell ((9209:ℚ)/12800) ((4633:ℚ)/6400) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source27 nn0 nn1 Qcell ((1857:ℚ)/2560) ((9323:ℚ)/12800) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source27 nn0 nn1 Qcell ((4633:ℚ)/6400) ((9323:ℚ)/12800) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source27 nn0 nn1 Qcell ((9209:ℚ)/12800) ((9323:ℚ)/12800) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source27 nn0 nn1 Qcell ((2269:ℚ)/3200) ((9323:ℚ)/12800) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((9323:ℚ)/12800) :=
  cell_join node0_10 node10_21
private theorem node21_23 :
    CellBound source27 nn0 nn1 Qcell ((9323:ℚ)/12800) ((9361:ℚ)/12800) :=
  cell_join leaf21 leaf22
private theorem node24_26 :
    CellBound source27 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_join leaf24 leaf25
private theorem node23_26 :
    CellBound source27 nn0 nn1 Qcell ((9361:ℚ)/12800) ((4709:ℚ)/6400) :=
  cell_join leaf23 node24_26
private theorem node21_26 :
    CellBound source27 nn0 nn1 Qcell ((9323:ℚ)/12800) ((4709:ℚ)/6400) :=
  cell_join node21_23 node23_26
private theorem node27_29 :
    CellBound source27 nn0 nn1 Qcell ((9437:ℚ)/12800) ((4747:ℚ)/6400) :=
  cell_join leaf27 leaf28
private theorem node26_29 :
    CellBound source27 nn0 nn1 Qcell ((4709:ℚ)/6400) ((4747:ℚ)/6400) :=
  cell_join leaf26 node27_29
private theorem node30_32 :
    CellBound source27 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join leaf30 leaf31
private theorem node29_32 :
    CellBound source27 nn0 nn1 Qcell ((4747:ℚ)/6400) ((1201:ℚ)/1600) :=
  cell_join leaf29 node30_32
private theorem node26_32 :
    CellBound source27 nn0 nn1 Qcell ((4709:ℚ)/6400) ((1201:ℚ)/1600) :=
  cell_join node26_29 node29_32
private theorem node21_32 :
    CellBound source27 nn0 nn1 Qcell ((9323:ℚ)/12800) ((1201:ℚ)/1600) :=
  cell_join node21_26 node26_32
private theorem node32_34 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_join leaf32 leaf33
private theorem node35_37 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf35 leaf36
private theorem node34_37 :
    CellBound source27 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf34 node35_37
private theorem node32_37 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node32_34 node34_37
private theorem node38_40 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((343:ℚ)/400) :=
  cell_join leaf38 leaf39
private theorem node37_40 :
    CellBound source27 nn0 nn1 Qcell ((1239:ℚ)/1600) ((343:ℚ)/400) :=
  cell_join leaf37 node38_40
private theorem node41_43 :
    CellBound source27 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf41 leaf42
private theorem node40_43 :
    CellBound source27 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf40 node41_43
private theorem node37_43 :
    CellBound source27 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node37_40 node40_43
private theorem node32_43 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node32_37 node37_43
private theorem node21_43 :
    CellBound source27 nn0 nn1 Qcell ((9323:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node21_32 node32_43
private theorem node0_43 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_21 node21_43
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_43
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32,packet33,packet34,packet35,packet36,packet37,packet38,packet39,packet40,packet41,packet42]
theorem packet_count : packets.length = 43 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC32
#check @N11Formalization.C450Source27GroupedC32.bound
#print axioms N11Formalization.C450Source27GroupedC32.valid0
#print axioms N11Formalization.C450Source27GroupedC32.valid1
#print axioms N11Formalization.C450Source27GroupedC32.valid2
#print axioms N11Formalization.C450Source27GroupedC32.valid3
#print axioms N11Formalization.C450Source27GroupedC32.valid4
#print axioms N11Formalization.C450Source27GroupedC32.valid5
#print axioms N11Formalization.C450Source27GroupedC32.valid6
#print axioms N11Formalization.C450Source27GroupedC32.valid7
#print axioms N11Formalization.C450Source27GroupedC32.valid8
#print axioms N11Formalization.C450Source27GroupedC32.valid9
#print axioms N11Formalization.C450Source27GroupedC32.valid10
#print axioms N11Formalization.C450Source27GroupedC32.valid11
#print axioms N11Formalization.C450Source27GroupedC32.valid12
#print axioms N11Formalization.C450Source27GroupedC32.valid13
#print axioms N11Formalization.C450Source27GroupedC32.valid14
#print axioms N11Formalization.C450Source27GroupedC32.valid15
#print axioms N11Formalization.C450Source27GroupedC32.valid16
#print axioms N11Formalization.C450Source27GroupedC32.valid17
#print axioms N11Formalization.C450Source27GroupedC32.valid18
#print axioms N11Formalization.C450Source27GroupedC32.valid19
#print axioms N11Formalization.C450Source27GroupedC32.valid20
#print axioms N11Formalization.C450Source27GroupedC32.valid21
#print axioms N11Formalization.C450Source27GroupedC32.valid22
#print axioms N11Formalization.C450Source27GroupedC32.valid23
#print axioms N11Formalization.C450Source27GroupedC32.valid24
#print axioms N11Formalization.C450Source27GroupedC32.valid25
#print axioms N11Formalization.C450Source27GroupedC32.valid26
#print axioms N11Formalization.C450Source27GroupedC32.valid27
#print axioms N11Formalization.C450Source27GroupedC32.valid28
#print axioms N11Formalization.C450Source27GroupedC32.valid29
#print axioms N11Formalization.C450Source27GroupedC32.valid30
#print axioms N11Formalization.C450Source27GroupedC32.valid31
#print axioms N11Formalization.C450Source27GroupedC32.valid32
#print axioms N11Formalization.C450Source27GroupedC32.valid33
#print axioms N11Formalization.C450Source27GroupedC32.valid34
#print axioms N11Formalization.C450Source27GroupedC32.valid35
#print axioms N11Formalization.C450Source27GroupedC32.valid36
#print axioms N11Formalization.C450Source27GroupedC32.valid37
#print axioms N11Formalization.C450Source27GroupedC32.valid38
#print axioms N11Formalization.C450Source27GroupedC32.valid39
#print axioms N11Formalization.C450Source27GroupedC32.valid40
#print axioms N11Formalization.C450Source27GroupedC32.valid41
#print axioms N11Formalization.C450Source27GroupedC32.valid42
#print axioms N11Formalization.C450Source27GroupedC32.bound
#print axioms N11Formalization.C450Source27GroupedC32.endpoint_checks
