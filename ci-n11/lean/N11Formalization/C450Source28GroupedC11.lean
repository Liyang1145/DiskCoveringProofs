import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6445786303:ℚ)/10000000000),((422760567:ℚ)/625000000),((-748281701:ℚ)/3100000000),((-2989786303:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5583512041:ℚ)/10000000000),((1084275404463840568710298565478210948045710351137263853729:ℚ)/5081180550000000000000000000000000000000000000000000000000),((-74772294220542453398866767:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6686244471:ℚ)/10000000000),((1721088709:ℚ)/2500000000),((-3083266127:ℚ)/12875000000),((-3230244471:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1238550577:ℚ)/2500000000),((311251483416030363750458558714450392652045807472213127843:ℚ)/1486187835587500000000000000000000000000000000000000000000),((-116554522068376537617805183:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6806391751:ℚ)/10000000000),((3472214023:ℚ)/5000000000),((-6256642069:ℚ)/26225000000),((-3350391751:ℚ)/21170000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2305339867:ℚ)/5000000000),((12912410322855064461872320590684337787933103448431868577861:ℚ)/62203966612731250000000000000000000000000000000000000000000),((-137628868555569463209055263:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((1373289251:ℚ)/2000000000),((7004488619:ℚ)/10000000000),((-12693465857:ℚ)/52925000000),((-682089251:ℚ)/4272000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4429766823:ℚ)/10000000000),((53551013203277950506472361698439910958068422798885431453:ℚ)/257890067654400000000000000000000000000000000000000000000),((-5928480145539432978640263:ℚ)/118292480000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((3463244233:ℚ)/5000000000),((110383389:ℚ)/156250000),((-201150167:ℚ)/834375000),((-1735244233:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4241714193:ℚ)/10000000000),((1693904557280395446928219501896742650382977689971989361:ℚ)/8154609144973754882812500000000000000000000000000000000),((-39706458555713559643403007:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1746629679:ℚ)/2500000000),((890571651:ℚ)/1250000000),((-1631714953:ℚ)/6734375000),((-882629679:ℚ)/5435000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2022760597:ℚ)/5000000000),((89867532819360461544608390978288356057568700238069226531:ℚ)/432469946713281250000000000000000000000000000000000000000),((-10591899942967561295956783:ℚ)/184832000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((3523268663:ℚ)/5000000000),((449037367:ℚ)/625000000),((-827112101:ℚ)/3396875000),((-105604039:ℚ)/645000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3839934989:ℚ)/10000000000),((31580818106953955098559685434493117205574846850676729:ℚ)/151917379101562500000000000000000000000000000000000000),((-45036433945555572035323647:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((1421308921:ℚ)/2000000000),((3622305597:ℚ)/5000000000),((-6706916791:ℚ)/27412500000),((-730108921:ℚ)/4424000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3623351531:ℚ)/10000000000),((1285450094503364584733094134513154549155457398227323761:ℚ)/6181057379350000000000000000000000000000000000000000000),((-7634075216754331040692383:ℚ)/118292480000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((7166540851:ℚ)/10000000000),((7364604989:ℚ)/10000000000),((-13773814967:ℚ)/55300000000),((-3710540851:ℚ)/22500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((678732033:ℚ)/2000000000),((96826272804152441679329675861822717611784327537273959411:ℚ)/461353683471679687500000000000000000000000000000000000000),((-201588867817181227088461863:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((1457300277:ℚ)/2000000000),((7484556839:ℚ)/10000000000),((-14133670517:ℚ)/56250000000),((-766100277:ℚ)/4576000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2882241161:ℚ)/10000000000),((1132013578922149563600631370005327699757184313714629623:ℚ)/5389898342400000000000000000000000000000000000000000000),((-8926220170285633286832727:ℚ)/118292480000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((925802639:ℚ)/1250000000),((1544868591:ℚ)/2000000000),((-2970605773:ℚ)/11440000000),((-493802639:ℚ)/2955000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2261847683:ℚ)/10000000000),((4147563349235730535101774996422337954409778173595419:ℚ)/19412079882812500000000000000000000000000000000000000),((-3825717192315150743613423:ℚ)/46208000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((955768271:ℚ)/1250000000),((7963984723:ℚ)/10000000000),((-15571954169:ℚ)/59100000000),((-523768271:ℚ)/3050000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((22416413152989756400992195671179095167849402408466188819:ℚ)/104801383593750000000000000000000000000000000000000000000),((-96999969:ℚ)/1024000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((3942865391:ℚ)/5000000000),((2110721713:ℚ)/2500000000),((-4252165139:ℚ)/15250000000),((-2214865391:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((61004203689395555448008920818845630591438997791838248483:ℚ)/276632755200000000000000000000000000000000000000000000000),((-96999969:ℚ)/1024000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((4182264451:ℚ)/5000000000),((414190201:ℚ)/400000000),((-909770603:ℚ)/2592000000),((-2454264451:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((527918741032576246854246689590265639272769513870821334569:ℚ)/2073600000000000000000000000000000000000000000000000000000),((-96999969:ℚ)/1024000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10276081597:ℚ)/10000000000),((1771079269:ℚ)/1250000000),((-4273237807:ℚ)/10000000000),((-6820081597:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((119530466649823704379195001731587168753549149169953720461:ℚ)/403671859200000000000000000000000000000000000000000000000),((-96999969:ℚ)/1024000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source28 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source28 nn0 nn1 Qcell ((2193:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source28 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC11
#check @N11Formalization.C450Source28GroupedC11.bound
#print axioms N11Formalization.C450Source28GroupedC11.valid0
#print axioms N11Formalization.C450Source28GroupedC11.valid1
#print axioms N11Formalization.C450Source28GroupedC11.valid2
#print axioms N11Formalization.C450Source28GroupedC11.valid3
#print axioms N11Formalization.C450Source28GroupedC11.valid4
#print axioms N11Formalization.C450Source28GroupedC11.valid5
#print axioms N11Formalization.C450Source28GroupedC11.valid6
#print axioms N11Formalization.C450Source28GroupedC11.valid7
#print axioms N11Formalization.C450Source28GroupedC11.valid8
#print axioms N11Formalization.C450Source28GroupedC11.valid9
#print axioms N11Formalization.C450Source28GroupedC11.valid10
#print axioms N11Formalization.C450Source28GroupedC11.valid11
#print axioms N11Formalization.C450Source28GroupedC11.valid12
#print axioms N11Formalization.C450Source28GroupedC11.valid13
#print axioms N11Formalization.C450Source28GroupedC11.valid14
#print axioms N11Formalization.C450Source28GroupedC11.bound
#print axioms N11Formalization.C450Source28GroupedC11.endpoint_checks
