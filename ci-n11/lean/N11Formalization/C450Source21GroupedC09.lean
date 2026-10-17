import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((811840009:ℚ)/1250000000),((1360021973:ℚ)/2000000000),((-1056021973:ℚ)/2480000000),((-4082880063:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((341298159:ℚ)/625000000),((46202785979819452572105226695037231660265826438991916633:ℚ)/413507531738281250000000000000000000000000000000000000000),((37754179519463029673143347:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6733621969:ℚ)/10000000000),((3459770471:ℚ)/5000000000),((-2699770471:ℚ)/6437500000),((-34335353783:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2410719351:ℚ)/5000000000),((20114260922158089525669266849714245963256291167859276986401:ℚ)/185773479448437500000000000000000000000000000000000000000000),((2325465480564426326236335907:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((6853034509:ℚ)/10000000000),((1407789517:ℚ)/2000000000),((-1103789517:ℚ)/2622500000),((-35171241563:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2235380273:ℚ)/5000000000),((71982973612763558310796258880427218418844134807287153479489:ℚ)/665561232900000000000000000000000000000000000000000000000000),((2279738732905158294572780347:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((1743105821:ℚ)/2500000000),((887330269:ℚ)/1250000000),((-232443423:ℚ)/556250000),((-9001740747:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4092384539:ℚ)/10000000000),((4526626705722823251369575764965825704174043341633108883:ℚ)/42471922630071640014648437500000000000000000000000000000),((139612144220121095995715867:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7032109157:ℚ)/10000000000),((447395693:ℚ)/625000000),((-352395693:ℚ)/841796875),((-36424764099:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3890297017:ℚ)/10000000000),((368619050032835368861125229741062782436681012739891099680341:ℚ)/3459759573706250000000000000000000000000000000000000000000000),((2210740354324138930882089163:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((3545894777:ℚ)/5000000000),((3609007271:ℚ)/5000000000),((-2849007271:ℚ)/6793750000),((-18421263439:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1838867033:ℚ)/5000000000),((3312356433140468893619440078606672468436718671995840184153:ℚ)/31098753480249023437500000000000000000000000000000000000000),((546907962837531536974503123:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7151464619:ℚ)/10000000000),((7277692657:ℚ)/10000000000),((-5757692657:ℚ)/13706250000),((-37260252333:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3452756687:ℚ)/10000000000),((30850576179956385248179349395116243102707032590089465313181:ℚ)/289737064657031250000000000000000000000000000000000000000000),((2164468758234645662544099307:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7211134491:ℚ)/10000000000),((733736557:ℚ)/1000000000),((-581736557:ℚ)/1382500000),((-37677941437:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3212752809:ℚ)/10000000000),((31916919331588688655499201102819557560623243344698154643309:ℚ)/299842983018701171875000000000000000000000000000000000000000),((6423753108036383508702579041:ℚ)/44359680000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((908849913:ℚ)/1250000000),((3698516707:ℚ)/5000000000),((-2938516707:ℚ)/6971875000),((-4761949391:ℚ)/14062500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((295405671:ℚ)/1000000000),((16118501895311005877672748163242382157086124831979701009:ℚ)/151470210403203964233398437500000000000000000000000000000),((99280249084712669458271609:ℚ)/693120000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((7330459187:ℚ)/10000000000),((3758177203:ℚ)/5000000000),((-999392401:ℚ)/2343750000),((-38513214309:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2671237181:ℚ)/10000000000),((3024260517509999830949217465384673789534139916864369127343:ℚ)/28072387200000000000000000000000000000000000000000000000000),((2094651555525212065827203003:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3724882329:ℚ)/5000000000),((484683809:ℚ)/625000000),((-389683809:ℚ)/893750000),((-19674176303:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1991646627:ℚ)/10000000000),((564808971304455626462521353852335455950980411337028530761:ℚ)/5124789089062500000000000000000000000000000000000000000000),((1535874844118309442947759801:ℚ)/11089920000000000000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((961040209:ℚ)/1250000000),((7993459359:ℚ)/10000000000),((-6473459359:ℚ)/14775000000),((-5127281463:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((1439812078222280174243997722696603170324409730137636348473:ℚ)/13100172949218750000000000000000000000000000000000000000000),((137711561:ℚ)/1024000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((317072497:ℚ)/400000000),((8470315981:ℚ)/10000000000),((-6950315981:ℚ)/15250000000),((-1707507479:ℚ)/5184000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((673597725666890446835687871000601431131150731216257379:ℚ)/5901498777600000000000000000000000000000000000000000000),((137711561:ℚ)/1024000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8403618647:ℚ)/10000000000),((10375971133:ℚ)/10000000000),((-8855971133:ℚ)/16200000000),((-46025330529:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((280459446564636855423059500861624059059795600699393167098361:ℚ)/2073600000000000000000000000000000000000000000000000000000000),((137711561:ℚ)/1024000000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((64432003:ℚ)/62500000),((7091298863:ℚ)/5000000000),((-6331298863:ℚ)/10000000000),((-371024021:ℚ)/1380000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((644946607547143908014500411901433894132354991946989:ℚ)/4106362500000000000000000000000000000000000000000000),((137711561:ℚ)/1024000000)⟩
theorem valid14 : Valid source21 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC09
#check @N11Formalization.C450Source21GroupedC09.bound
#print axioms N11Formalization.C450Source21GroupedC09.valid0
#print axioms N11Formalization.C450Source21GroupedC09.valid1
#print axioms N11Formalization.C450Source21GroupedC09.valid2
#print axioms N11Formalization.C450Source21GroupedC09.valid3
#print axioms N11Formalization.C450Source21GroupedC09.valid4
#print axioms N11Formalization.C450Source21GroupedC09.valid5
#print axioms N11Formalization.C450Source21GroupedC09.valid6
#print axioms N11Formalization.C450Source21GroupedC09.valid7
#print axioms N11Formalization.C450Source21GroupedC09.valid8
#print axioms N11Formalization.C450Source21GroupedC09.valid9
#print axioms N11Formalization.C450Source21GroupedC09.valid10
#print axioms N11Formalization.C450Source21GroupedC09.valid11
#print axioms N11Formalization.C450Source21GroupedC09.valid12
#print axioms N11Formalization.C450Source21GroupedC09.valid13
#print axioms N11Formalization.C450Source21GroupedC09.valid14
#print axioms N11Formalization.C450Source21GroupedC09.bound
#print axioms N11Formalization.C450Source21GroupedC09.endpoint_checks
