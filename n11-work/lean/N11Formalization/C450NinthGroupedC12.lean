import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((3132034871:ℚ)/5000000000),((6530319299:ℚ)/10000000000),((-5634319299:ℚ)/19840000000),((-2492034871:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6019734713:ℚ)/10000000000),((27538071957963363973118752015396517644461132505530114131:ℚ)/1240522595214843750000000000000000000000000000000000000000),((136437095573678825481834061:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((3250894363:ℚ)/5000000000),((3384037531:ℚ)/5000000000),((-2936037531:ℚ)/10300000000),((-870298121:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2721417513:ℚ)/5000000000),((312733841482964421828367697037950913097517737509199431:ℚ)/14181993554687500000000000000000000000000000000000000000),((33457327118452269157248221:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6739492107:ℚ)/10000000000),((1721736557:ℚ)/2500000000),((-499245519:ℚ)/1780000000),((-5459492107:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2402377169:ℚ)/5000000000),((241223110994219498408027789567437218848018432520468477339:ℚ)/11162942360058593750000000000000000000000000000000000000000),((8182895839736960011260589:ℚ)/184832000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((6858338459:ℚ)/10000000000),((875726653:ℚ)/1250000000),((-763726653:ℚ)/2717500000),((-5578338459:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((890918163:ℚ)/2000000000),((48378755172824720767504628137526747826231194642591601909:ℚ)/2243959396960449218750000000000000000000000000000000000000),((2025564910448454674894349:ℚ)/46208000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((872147687:ℚ)/1250000000),((282609809:ℚ)/400000000),((-246769809:ℚ)/884800000),((-712147687:ℚ)/3485937500),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((31848607:ℚ)/78125000),((195469762771032842590079217824256498865119599176938267:ℚ)/9150481659506261348724365234375000000000000000000000000),((205103234595887278511941:ℚ)/4731699200000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((219893807:ℚ)/312500000),((7124676263:ℚ)/10000000000),((-6228676263:ℚ)/22310000000),((-179893807:ℚ)/878906250),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3783869:ℚ)/9765625),((591915730841140034218894381175758859000963459903527:ℚ)/27735023877539788372814655303955078125000000000000000),((127547854737000812190458709:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-5:ℚ)/16),((-1:ℚ)/4),((7096021387:ℚ)/10000000000),((1788597857:ℚ)/2500000000),((-521532619:ℚ)/1875000000),((-5816021387:ℚ)/28243750000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((732443147:ℚ)/2000000000),((2992039619430380361882830575088703064732052607192152899:ℚ)/140814407896423339843750000000000000000000000000000000000),((7926609332796493415250789:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7125730887:ℚ)/10000000000),((179602659:ℚ)/250000000),((-157202659:ℚ)/564875000),((-5845730887:ℚ)/28362500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((1775723693:ℚ)/5000000000),((34216556707361125699349552112109843060196672046988908441:ℚ)/1611001311693450927734375000000000000000000000000000000000),((237198320446793181061223:ℚ)/5544960000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-5:ℚ)/16),((-1:ℚ)/4),((3577720101:ℚ)/5000000000),((901727633:ℚ)/1250000000),((-789727633:ℚ)/2836250000),((-2937720101:ℚ)/14240625000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((687453553:ℚ)/2000000000),((289830758539559134616878714506778759959168818466189495619:ℚ)/13651501127651023864746093750000000000000000000000000000000),((1971658334511097803519429:ℚ)/46208000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((1437029867:ℚ)/2000000000),((3621767771:ℚ)/5000000000),((-3173767771:ℚ)/11392500000),((-1181029867:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3319324329:ℚ)/10000000000),((37706571481161776336252994488295581144737010098868361029:ℚ)/1776748173200000000000000000000000000000000000000000000000),((31466709198298245246257501:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-5:ℚ)/16),((-1:ℚ)/4),((7214858289:ℚ)/10000000000),((1818312449:ℚ)/2500000000),((-1594312449:ℚ)/5720000000),((-5934858289:ℚ)/28718750000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((199825001:ℚ)/625000000),((1347272937626301365965932314846412269507055893450809011133:ℚ)/63508800279808044433593750000000000000000000000000000000000),((7846742563480204065252261:ℚ)/184832000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((905570883:ℚ)/1250000000),((7302963829:ℚ)/10000000000),((-6406963829:ℚ)/22975000000),((-745570883:ℚ)/3604687500),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((767598857:ℚ)/2500000000),((668552059682236761408372291533777612358345215290657:ℚ)/31526784614986740052700042724609375000000000000000000),((125229266076926400118338301:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((1454855133:ℚ)/2000000000),((1472478249:ℚ)/2000000000),((-1293278249:ℚ)/4614000000),((-1198855133:ℚ)/5815000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2938304081:ℚ)/10000000000),((20100885053351065384294150989069382095192813326267515309:ℚ)/945051583939843750000000000000000000000000000000000000000),((14999378996555001388773983:ℚ)/354877440000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((1833423087:ℚ)/2500000000),((7421817811:ℚ)/10000000000),((-6525817811:ℚ)/23260000000),((-1513423087:ℚ)/7328125000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1327536323:ℚ)/5000000000),((182383663794348079747883576480091625654736525599776171751:ℚ)/8581428592228889465332031250000000000000000000000000000000),((124359975758124665788385581:ℚ)/2957312000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((1478621671:ℚ)/2000000000),((3740621773:ℚ)/5000000000),((-470374539:ℚ)/1675000000),((-407540557:ℚ)/1970000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2338674881:ℚ)/10000000000),((16998072940596087464170449620124309993637580110314127:ℚ)/800374985937500000000000000000000000000000000000000000),((30931622340532337761474669:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3726261851:ℚ)/5000000000),((3800046303:ℚ)/5000000000),((-3352046303:ℚ)/11820000000),((-3086261851:ℚ)/15012500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((394642729:ℚ)/2000000000),((66735360594363421923605097966087364839297558057244335157:ℚ)/3124399561129760742187500000000000000000000000000000000000),((2027415094249693:ℚ)/48640000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((47320953:ℚ)/62500000),((7718938577:ℚ)/10000000000),((-6822938577:ℚ)/24020000000),((-39320953:ℚ)/190625000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((54283551:ℚ)/625000000),((3326844400708232172653440482753625073575520383887947:ℚ)/155985363578796386718750000000000000000000000000000000),((25012302342529:ℚ)/608000000000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((7690178801:ℚ)/10000000000),((8194294289:ℚ)/10000000000),((-7298294289:ℚ)/24400000000),((-712242089:ℚ)/3600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((130742224786047153245176871500649702731720379679820951:ℚ)/5929200000000000000000000000000000000000000000000000000),((8398367:ℚ)/204800000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((8165461689:ℚ)/10000000000),((2019075787:ℚ)/2000000000),((-204430643:ℚ)/576000000),((-6885461689:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((9736320073598518976047688814174827828734297458963281713:ℚ)/400000000000000000000000000000000000000000000000000000000),((8398367:ℚ)/204800000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((5033162161:ℚ)/5000000000),((1389665177:ℚ)/1000000000),((-1300065177:ℚ)/3200000000),((-1464387387:ℚ)/9200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((33301079448657250335482982191694537171865229454001411:ℚ)/1216700000000000000000000000000000000000000000000000000),((8398367:ℚ)/204800000)⟩
theorem valid19 : Valid ninth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC12
#check @N11Formalization.C450NinthGroupedC12.bound
#print axioms N11Formalization.C450NinthGroupedC12.valid0
#print axioms N11Formalization.C450NinthGroupedC12.valid1
#print axioms N11Formalization.C450NinthGroupedC12.valid2
#print axioms N11Formalization.C450NinthGroupedC12.valid3
#print axioms N11Formalization.C450NinthGroupedC12.valid4
#print axioms N11Formalization.C450NinthGroupedC12.valid5
#print axioms N11Formalization.C450NinthGroupedC12.valid6
#print axioms N11Formalization.C450NinthGroupedC12.valid7
#print axioms N11Formalization.C450NinthGroupedC12.valid8
#print axioms N11Formalization.C450NinthGroupedC12.valid9
#print axioms N11Formalization.C450NinthGroupedC12.valid10
#print axioms N11Formalization.C450NinthGroupedC12.valid11
#print axioms N11Formalization.C450NinthGroupedC12.valid12
#print axioms N11Formalization.C450NinthGroupedC12.valid13
#print axioms N11Formalization.C450NinthGroupedC12.valid14
#print axioms N11Formalization.C450NinthGroupedC12.valid15
#print axioms N11Formalization.C450NinthGroupedC12.valid16
#print axioms N11Formalization.C450NinthGroupedC12.valid17
#print axioms N11Formalization.C450NinthGroupedC12.valid18
#print axioms N11Formalization.C450NinthGroupedC12.valid19
#print axioms N11Formalization.C450NinthGroupedC12.bound
#print axioms N11Formalization.C450NinthGroupedC12.endpoint_checks
