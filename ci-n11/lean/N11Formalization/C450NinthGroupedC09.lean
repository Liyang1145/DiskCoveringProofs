import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((6317385489:ℚ)/10000000000),((1647883047:ℚ)/2500000000),((-1507883047:ℚ)/3100000000),((-39101698423:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2947354507:ℚ)/5000000000),((14199212003233152070376534166160472390628816656835673343507:ℚ)/635147568750000000000000000000000000000000000000000000000000),((273670118687746205766841:ℚ)/2707500000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((6555074327:ℚ)/10000000000),((853655589:ℚ)/1250000000),((-783655589:ℚ)/1609375000),((-13588506763:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5305877787:ℚ)/10000000000),((161930523788623918260767068639472382333623639126180587437:ℚ)/7261180700000000000000000000000000000000000000000000000000),((68132308162582093628029:ℚ)/676875000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((424546857:ℚ)/625000000),((1389619079:ℚ)/2000000000),((-1277619079:ℚ)/2670000000),((-2651827999:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4650863149:ℚ)/10000000000),((3780321209206152918341649511434042970341521584199871527:ℚ)/174420974375915527343750000000000000000000000000000000000),((57824792733038715874403:ℚ)/577600000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6911582801:ℚ)/10000000000),((7007519427:ℚ)/10000000000),((-6447519427:ℚ)/13587500000),((-14420359869:ℚ)/36550000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((214455973:ℚ)/500000000),((1772896605288355874327436262499428022231490567879088547211:ℚ)/82930009280664062500000000000000000000000000000000000000000),((4325092363715438026326721:ℚ)/43320000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((1394199653:ℚ)/2000000000),((1413388523:ℚ)/2000000000),((-1301388523:ℚ)/2741250000),((-8735397571:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4097094157:ℚ)/10000000000),((49550480461447505956632094633613014271208413519687310259:ℚ)/2317896517256250000000000000000000000000000000000000000000),((57608845256301390384507:ℚ)/577600000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7030413033:ℚ)/10000000000),((7126364981:ℚ)/10000000000),((-6566364981:ℚ)/13825000000),((-44092891231:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((974044197:ℚ)/2500000000),((6409551359267687896018944598750339884161189119621380558199:ℚ)/299842983018701171875000000000000000000000000000000000000000),((1438752942542332625538363:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((3544913561:ℚ)/5000000000),((7156075863:ℚ)/10000000000),((-6596075863:ℚ)/13943750000),((-22254394927:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3684909221:ℚ)/10000000000),((2081507414679314336031831280773716478108513428678110637449:ℚ)/98015430042026855468750000000000000000000000000000000000000),((4310409020452268610758281:ℚ)/43320000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((3559766959:ℚ)/5000000000),((7185786547:ℚ)/10000000000),((-6625786547:ℚ)/14003125000),((-7452789571:ℚ)/18750000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((893705741:ℚ)/2500000000),((45944160030561398260901804540274553881478876303936917241:ℚ)/2163416147232055664062500000000000000000000000000000000000),((1436074002611971095295947:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((7149240551:ℚ)/10000000000),((1443099407:ℚ)/2000000000),((-1331099407:ℚ)/2812500000),((-44924683857:ℚ)/112975000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3461392657:ℚ)/10000000000),((574175402775948624194899569122280501880616945472916441507:ℚ)/27036366316113281250000000000000000000000000000000000000000),((57413881260844599812467:ℚ)/577600000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7178947023:ℚ)/10000000000),((7245207331:ℚ)/10000000000),((-6685207331:ℚ)/14121875000),((-45132629161:ℚ)/113450000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((1672138761:ℚ)/5000000000),((2189663775558804237235820223156339641139409403115469504407:ℚ)/103104083948380859375000000000000000000000000000000000000000),((1434622093489261339713963:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((901081667:ℚ)/1250000000),((7274917437:ℚ)/10000000000),((-6714917437:ℚ)/14181250000),((-5667571669:ℚ)/14240625000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3223075361:ℚ)/10000000000),((289925614130801199659770237855359722387200278927731873971:ℚ)/13651501127651023864746093750000000000000000000000000000000),((4301697565285365772294081:ℚ)/43320000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((1809589873:ℚ)/2500000000),((1460925471:ℚ)/2000000000),((-1348925471:ℚ)/2848125000),((-11387129111:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((619461171:ℚ)/2000000000),((4716784113531847823401981810665034714824189510111730010673:ℚ)/222093521650000000000000000000000000000000000000000000000000),((171981397950154636279609:ℚ)/1732800000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7268065493:ℚ)/10000000000),((1841011659:ℚ)/2500000000),((-1701011659:ℚ)/3575000000),((-15252152817:ℚ)/38450000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2966387533:ℚ)/10000000000),((42412940029062167905076611115261152476237980138294607:ℚ)/1984564059051513671875000000000000000000000000000000000),((268680284252675898687169:ℚ)/2707500000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7327477037:ℚ)/10000000000),((927933149:ℚ)/1250000000),((-857933149:ℚ)/1802343750),((-46172339259:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2686062567:ℚ)/10000000000),((161565656088425827983672257728993615482626139597439466195803:ℚ)/7560412671518750000000000000000000000000000000000000000000000),((22367718566618439966583:ℚ)/225625000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((461680499:ℚ)/625000000),((7542300203:ℚ)/10000000000),((-6982300203:ℚ)/14537500000),((-970587831:ℚ)/2462500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2373735191:ℚ)/10000000000),((586823032884556119506130884980149988716797092008413661:ℚ)/27134914547729492187500000000000000000000000000000000000),((1431140960013370526109947:ℚ)/14440000000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((3752854071:ℚ)/5000000000),((7779962273:ℚ)/10000000000),((-2406654091:ℚ)/4925000000),((-23709978497:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1576868007:ℚ)/10000000000),((18537565156162439008696251881527298661417842691582917277791:ℚ)/838411068750000000000000000000000000000000000000000000000000),((75119483267351:ℚ)/760000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((7743341897:ℚ)/10000000000),((4127628937:ℚ)/5000000000),((-3847628937:ℚ)/7625000000),((-16361131093:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((235440445266031738595130587279221293605371099780355050403:ℚ)/10245657600000000000000000000000000000000000000000000000000),((197147:ℚ)/2000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8218585857:ℚ)/10000000000),((2031231853:ℚ)/2000000000),((-639743951:ℚ)/1080000000),((-52410100999:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6286210331081388221136230482590541756909432805165381980807:ℚ)/230400000000000000000000000000000000000000000000000000000000),((197147:ℚ)/2000000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((10119329807:ℚ)/10000000000),((13957217113:ℚ)/10000000000),((-13397217113:ℚ)/20000000000),((-21905102883:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((19647084986378389127327365615724122735535588308719164219:ℚ)/622950400000000000000000000000000000000000000000000000000),((197147:ℚ)/2000000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC09
#check @N11Formalization.C450NinthGroupedC09.bound
#print axioms N11Formalization.C450NinthGroupedC09.valid0
#print axioms N11Formalization.C450NinthGroupedC09.valid1
#print axioms N11Formalization.C450NinthGroupedC09.valid2
#print axioms N11Formalization.C450NinthGroupedC09.valid3
#print axioms N11Formalization.C450NinthGroupedC09.valid4
#print axioms N11Formalization.C450NinthGroupedC09.valid5
#print axioms N11Formalization.C450NinthGroupedC09.valid6
#print axioms N11Formalization.C450NinthGroupedC09.valid7
#print axioms N11Formalization.C450NinthGroupedC09.valid8
#print axioms N11Formalization.C450NinthGroupedC09.valid9
#print axioms N11Formalization.C450NinthGroupedC09.valid10
#print axioms N11Formalization.C450NinthGroupedC09.valid11
#print axioms N11Formalization.C450NinthGroupedC09.valid12
#print axioms N11Formalization.C450NinthGroupedC09.valid13
#print axioms N11Formalization.C450NinthGroupedC09.valid14
#print axioms N11Formalization.C450NinthGroupedC09.valid15
#print axioms N11Formalization.C450NinthGroupedC09.valid16
#print axioms N11Formalization.C450NinthGroupedC09.valid17
#print axioms N11Formalization.C450NinthGroupedC09.valid18
#print axioms N11Formalization.C450NinthGroupedC09.bound
#print axioms N11Formalization.C450NinthGroupedC09.endpoint_checks
