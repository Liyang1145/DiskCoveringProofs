import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((20237801:ℚ)/31250000),((1696655477:ℚ)/2500000000),((-8356588339:ℚ)/24800000000),((-37713403:ℚ)/160937500),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5507773823:ℚ)/10000000000),((265816046117779307156823770768832137976629604297919:ℚ)/1211447846889495849609375000000000000000000000000000),((28091095320540295869:ℚ)/722000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6715601477:ℚ)/10000000000),((6906346581:ℚ)/10000000000),((-34264426067:ℚ)/103000000000),((-12786804431:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((243616423:ℚ)/500000000),((2485665994712762140526401125947762895686912264900271030613:ℚ)/11610842465527343750000000000000000000000000000000000000000),((2070945621572357347065601:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6835298919:ℚ)/10000000000),((3513018081:ℚ)/5000000000),((-17551126567:ℚ)/52450000000),((-13145896757:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4524438211:ℚ)/10000000000),((26669543269874788437091066870481174742262148256443673120793:ℚ)/124792731168750000000000000000000000000000000000000000000000),((1664769834820943941811609:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((3477481131:ℚ)/5000000000),((3542934191:ℚ)/5000000000),((-5920179779:ℚ)/17800000000),((-6752443393:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1037436177:ℚ)/2500000000),((13461126388743531222055329085626685135826894074896669431:ℚ)/63707883945107460021972656250000000000000000000000000000),((314082881262279311423009:ℚ)/18483200000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((7014781717:ℚ)/10000000000),((7145692519:ℚ)/10000000000),((-35939847633:ℚ)/107750000000),((-13684345151:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((987493309:ℚ)/2500000000),((45660205602830311073190517241815013487268134505513893070669:ℚ)/216234973356640625000000000000000000000000000000000000000000),((1051262600291238623102241:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3537296659:ℚ)/5000000000),((7205508787:ℚ)/10000000000),((-36358561509:ℚ)/108700000000),((-6931889977:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((467520143:ℚ)/1250000000),((1230532199495956008618053782177189233423712762617299078233:ℚ)/5831016277546691894531250000000000000000000000000000000000),((211406621571165387246289:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((891799659:ℚ)/1250000000),((726531739:ℚ)/1000000000),((-1225907391:ℚ)/3655000000),((-1755398977:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3518507593:ℚ)/10000000000),((1065649042861320812422271597093546623151772058313411027:ℚ)/5052613432216644287109375000000000000000000000000000000),((9990979723349832172289:ℚ)/1155200000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3597096889:ℚ)/5000000000),((7325118529:ℚ)/10000000000),((-37195829703:ℚ)/110600000000),((-7111290667:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((656521871:ℚ)/2000000000),((493791442411059182763932696755657471859651310158849692799:ℚ)/2342523304833602905273437500000000000000000000000000000000),((108162696758971667529049:ℚ)/18483200000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7253983029:ℚ)/10000000000),((1476982479:ℚ)/2000000000),((-7522877353:ℚ)/22310000000),((-14401949087:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((605826909:ℚ)/2000000000),((3063594392482076367688847961331782803789137496342409946951:ℚ)/14541140198707580566406250000000000000000000000000000000000),((225310292129182319736929:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((7313765211:ℚ)/10000000000),((23451497:ℚ)/31250000),((-40053493:ℚ)/117187500),((-14581295633:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((688306673:ℚ)/2500000000),((372869563734277210631722293292194531525595763572463979839:ℚ)/1754524200000000000000000000000000000000000000000000000000),((17400785881870912646849:ℚ)/73932800000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((3716654543:ℚ)/5000000000),((3871766399:ℚ)/5000000000),((-20062364793:ℚ)/57200000000),((-7469963629:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1049134489:ℚ)/5000000000),((5322268242083123934408039260990686455945369240262281539:ℚ)/24638409082031250000000000000000000000000000000000000000),((-277096214260127814879:ℚ)/51200000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((7672319539:ℚ)/10000000000),((7982488871:ℚ)/10000000000),((-41797422097:ℚ)/118200000000),((-15656958617:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((30106139410867211431592164233499525389167636391000763267849:ℚ)/139735178125000000000000000000000000000000000000000000000000),((-853779:ℚ)/64000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((1582247011:ℚ)/2000000000),((338405709:ℚ)/400000000),((-1805639963:ℚ)/4880000000),((-3274741033:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((30657996127011430070474984415781407764247002817541307611:ℚ)/138316377600000000000000000000000000000000000000000000000),((-853779:ℚ)/64000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((8388815047:ℚ)/10000000000),((2592055391:ℚ)/2500000000),((-14624387737:ℚ)/32400000000),((-17806445141:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((32957323595675201033218399926581592352739602198974528903089:ℚ)/129600000000000000000000000000000000000000000000000000000000),((-853779:ℚ)/64000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((10296669451:ℚ)/10000000000),((14177680809:ℚ)/10000000000),((-85163765663:ℚ)/160000000000),((-23530008353:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((920780520073688993574444489549295050293389222884952575479:ℚ)/3153686400000000000000000000000000000000000000000000000000),((-853779:ℚ)/64000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC10
#check @N11Formalization.C450Source24GroupedC10.bound
#print axioms N11Formalization.C450Source24GroupedC10.valid0
#print axioms N11Formalization.C450Source24GroupedC10.valid1
#print axioms N11Formalization.C450Source24GroupedC10.valid2
#print axioms N11Formalization.C450Source24GroupedC10.valid3
#print axioms N11Formalization.C450Source24GroupedC10.valid4
#print axioms N11Formalization.C450Source24GroupedC10.valid5
#print axioms N11Formalization.C450Source24GroupedC10.valid6
#print axioms N11Formalization.C450Source24GroupedC10.valid7
#print axioms N11Formalization.C450Source24GroupedC10.valid8
#print axioms N11Formalization.C450Source24GroupedC10.valid9
#print axioms N11Formalization.C450Source24GroupedC10.valid10
#print axioms N11Formalization.C450Source24GroupedC10.valid11
#print axioms N11Formalization.C450Source24GroupedC10.valid12
#print axioms N11Formalization.C450Source24GroupedC10.valid13
#print axioms N11Formalization.C450Source24GroupedC10.valid14
#print axioms N11Formalization.C450Source24GroupedC10.bound
#print axioms N11Formalization.C450Source24GroupedC10.endpoint_checks
