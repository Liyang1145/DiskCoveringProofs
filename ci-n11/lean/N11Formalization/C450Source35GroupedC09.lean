import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6662818909:ℚ)/10000000000),((3444005541:ℚ)/5000000000),((-2124005541:ℚ)/6200000000),((-24609033:ℚ)/100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5018654347:ℚ)/10000000000),((137101776349507307013718354598223:ℚ)/581855468750000000000000000000000),((178057566457398802003433159:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6783763593:ℚ)/10000000000),((868554387:ℚ)/1250000000),((-179518129:ℚ)/526562500),((-1978949627:ℚ)/7850000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((467715737:ℚ)/1000000000),((13283306978284826684423423083706075662388077429309:ℚ)/57030846178531646728515625000000000000000000000000),((171272470473795131922610111:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((855525557:ℚ)/1250000000),((1752209813:ℚ)/2500000000),((-1092209813:ℚ)/3189062500),((-3268678899:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((899511951:ℚ)/2000000000),((145521185996888848853891607464209003433842042994381:ℚ)/623714367866516113281250000000000000000000000000000),((2622677954597971630063511:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((1380925027:ℚ)/2000000000),((1413844823:ℚ)/2000000000),((-885844823:ℚ)/2575000000),((-5314475189:ℚ)/20790000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((862215961:ℚ)/2000000000),((97421194803040053193877258526413957180691539985983:ℚ)/416842269897460937500000000000000000000000000000000),((6576450708267000778268231:ℚ)/36966400000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((3482513101:ℚ)/5000000000),((7129590227:ℚ)/10000000000),((-4489590227:ℚ)/12993750000),((-13497591707:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4116776241:ℚ)/10000000000),((1544007918152678062171674508145016211794821875072717:ℚ)/6595216369628906250000000000000000000000000000000000),((40238023419997671696488039:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((702540821:ℚ)/1000000000),((1797484527:ℚ)/2500000000),((-1137484527:ℚ)/3278125000),((-2741785747:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1956738803:ℚ)/5000000000),((51631379441865598199989291978279807560882247469720847:ℚ)/220169191169738769531250000000000000000000000000000000),((1574738547104485384291799:ℚ)/9241600000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((7085771687:ℚ)/10000000000),((3625134131:ℚ)/5000000000),((-2305134131:ℚ)/6615625000),((-27840401809:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((924923713:ℚ)/2500000000),((106273461590530548209609304031244926199639100489331331:ℚ)/452410488748550415039062500000000000000000000000000000),((153976539202465666529090591:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((3573058573:ℚ)/5000000000),((1827645293:ℚ)/2500000000),((-1167645293:ℚ)/3337500000),((-14131410011:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((868371481:ℚ)/2500000000),((18224193376649326786040910014796873331360022753034719:ℚ)/77450207519531250000000000000000000000000000000000000),((37615033931633542168966631:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7206445079:ℚ)/10000000000),((921359663:ℚ)/1250000000),((-591359663:ℚ)/1683593750),((-28685115553:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3232235791:ℚ)/10000000000),((3514957719429619584960022347107240446032620026013749:ℚ)/14912894181907176971435546875000000000000000000000000),((146924633397392871662457599:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7266755959:ℚ)/10000000000),((3745710509:ℚ)/5000000000),((-2425710509:ℚ)/6793750000),((-29107291713:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1486138291:ℚ)/5000000000),((29295265986484048867899974871314004499870154205147221:ℚ)/122486639308929443359375000000000000000000000000000000),((143370021791325156462029759:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((7387328373:ℚ)/10000000000),((386616293:ℚ)/500000000),((-254616293:ℚ)/691250000),((-2303946047:ℚ)/8800000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((237126973:ℚ)/1000000000),((72501444972433561514619595036010764305738495175019:ℚ)/294908581542968750000000000000000000000000000000000),((136203430597675390683127831:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((7628287631:ℚ)/10000000000),((1086739113:ℚ)/1250000000),((-58210701:ℚ)/137500000),((-31638013417:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1136678647433969116644499620540207956624167041741:ℚ)/4061889648437500000000000000000000000000000000000),((1708681:ℚ)/12800000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((107375741:ℚ)/125000000),((10610397779:ℚ)/10000000000),((-7970397779:ℚ)/16200000000),((-479630187:ℚ)/2000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((174456591907492028042208296650808905050507641833347497:ℚ)/553584375000000000000000000000000000000000000000000000),((1708681:ℚ)/12800000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((656675339:ℚ)/625000000),((14429647271:ℚ)/10000000000),((-11789647271:ℚ)/20000000000),((-3236727373:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((19365451585220172735937240520172947:ℚ)/50000000000000000000000000000000000),((1708681:ℚ)/12800000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC09
#check @N11Formalization.C450Source35GroupedC09.bound
#print axioms N11Formalization.C450Source35GroupedC09.valid0
#print axioms N11Formalization.C450Source35GroupedC09.valid1
#print axioms N11Formalization.C450Source35GroupedC09.valid2
#print axioms N11Formalization.C450Source35GroupedC09.valid3
#print axioms N11Formalization.C450Source35GroupedC09.valid4
#print axioms N11Formalization.C450Source35GroupedC09.valid5
#print axioms N11Formalization.C450Source35GroupedC09.valid6
#print axioms N11Formalization.C450Source35GroupedC09.valid7
#print axioms N11Formalization.C450Source35GroupedC09.valid8
#print axioms N11Formalization.C450Source35GroupedC09.valid9
#print axioms N11Formalization.C450Source35GroupedC09.valid10
#print axioms N11Formalization.C450Source35GroupedC09.valid11
#print axioms N11Formalization.C450Source35GroupedC09.valid12
#print axioms N11Formalization.C450Source35GroupedC09.valid13
#print axioms N11Formalization.C450Source35GroupedC09.bound
#print axioms N11Formalization.C450Source35GroupedC09.endpoint_checks
