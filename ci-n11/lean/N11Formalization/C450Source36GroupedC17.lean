import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(0:ℚ),((1:ℚ)/16),((2976500661:ℚ)/5000000000),((3146101011:ℚ)/5000000000),((544:ℚ)/2575),((14346101011:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6708562691:ℚ)/10000000000),((-4426990640116453115756806940981989074561853:ℚ)/20162124422400000000000000000000000000000000),((-196241732880413219811446341:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((6196532341:ℚ)/10000000000),((641364281:ℚ)/1000000000),((1088:ℚ)/5245),((2881364281:ℚ)/10300000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((3087459387:ℚ)/5000000000),((-33035756912229901974393271316074631337178941:ℚ)/153077347065512500000000000000000000000000000),((-8159922583623216764639981:ℚ)/36966400000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((394883001:ℚ)/625000000),((65349847:ℚ)/100000000),((272:ℚ)/1335),((289349847:ℚ)/1049000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((5892951323:ℚ)/10000000000),((-27741504096883892118141942883956129586153:ℚ)/130907574996018750000000000000000000000000),((-82979028642250996323789:ℚ)/369664000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),(0:ℚ),((1:ℚ)/16),((3219809453:ℚ)/5000000000),((1319124053:ℚ)/2000000000),((2176:ℚ)/10775),((1933041351:ℚ)/7120000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2799405369:ℚ)/5000000000),((-9997708270455555933001817898828399237350779:ℚ)/47563421378325000000000000000000000000000000),((-33808484483991194618495189:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((6500326869:ℚ)/10000000000),((6656233101:ℚ)/10000000000),((1088:ℚ)/5435),((29056233101:ℚ)/107750000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5446548597:ℚ)/10000000000),((-7767969990401221901635404406020745896518158939:ℚ)/37278909406684843750000000000000000000000000000),((-852061205885916365705446021:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((1640252689:ℚ)/2500000000),((268672953:ℚ)/400000000),((128:ℚ)/645),((1164672953:ℚ)/4348000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((5290421717:ℚ)/10000000000),((-17467723919385745955968603522672355791891:ℚ)/84548705834700000000000000000000000000000),((-1374227205294854796116589:ℚ)/5914624000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((3310835611:ℚ)/5000000000),((677739303:ℚ)/1000000000),((544:ℚ)/2765),((2917739303:ℚ)/10965000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2565035877:ℚ)/5000000000),((-433912841035560394855163416138321233881971:ℚ)/2117977942642898437500000000000000000000000),((-8657045965909466012054189:ℚ)/36966400000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((3341154447:ℚ)/5000000000),((6837941287:ℚ)/10000000000),((2176:ℚ)/11155),((29237941287:ℚ)/110600000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((620635503:ℚ)/1250000000),((-2464274683151565717397697359208243997018770467:ℚ)/12128048977140425000000000000000000000000000000),((-872499074032375269996203949:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((3371462191:ℚ)/5000000000),((6898469149:ℚ)/10000000000),((1088:ℚ)/5625),((29298469149:ℚ)/111550000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4794974189:ℚ)/10000000000),((-13390826112541726656270321454246369476077357:ℚ)/66439749188232421875000000000000000000000000),((-879275521476184553842714021:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((6803518269:ℚ)/10000000000),((3509732897:ℚ)/5000000000),((136:ℚ)/715),((4903244299:ℚ)/18750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((923834139:ℚ)/2000000000),((-509569247442481411358547617464696559246609:ℚ)/2570103808593750000000000000000000000000000),((-221061601064367898656316989:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((3462321741:ℚ)/5000000000),((3630618277:ℚ)/5000000000),((544:ℚ)/2955),((14830618277:ℚ)/57200000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2123804411:ℚ)/5000000000),((-18028773412488273475852448757519793500585467:ℚ)/93804139486200000000000000000000000000000000),((-223500120562968967812571509:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((447916143:ℚ)/625000000),((937841813:ℚ)/1250000000),((272:ℚ)/1525),((1245947271:ℚ)/4925000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3393195949:ℚ)/10000000000),((-7719094110589209714324814430457125461829:ℚ)/41291745135937500000000000000000000000000),((-14383382689233005845806549:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((1481676857:ℚ)/2000000000),((7985010961:ℚ)/10000000000),((68:ℚ)/405),((30385010961:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2250300339:ℚ)/10000000000),((-1169671545608254509975217765271458309505671:ℚ)/6591639870000000000000000000000000000000000),((-50077063302209021:ℚ)/194560000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((7891074823:ℚ)/10000000000),((4953544187:ℚ)/5000000000),((17:ℚ)/125),((1794838243:ℚ)/7200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-820086016077741080794335844853329697:ℚ)/5400000000000000000000000000000000000),((-67759169:ℚ)/256000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((4907200823:ℚ)/5000000000),((13732821999:ℚ)/10000000000),((34:ℚ)/345),((36132821999:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-3938592375375614044951290705873325865149771:ℚ)/31536864000000000000000000000000000000000000),((-67759169:ℚ)/256000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC17
#check @N11Formalization.C450Source36GroupedC17.bound
#print axioms N11Formalization.C450Source36GroupedC17.valid0
#print axioms N11Formalization.C450Source36GroupedC17.valid1
#print axioms N11Formalization.C450Source36GroupedC17.valid2
#print axioms N11Formalization.C450Source36GroupedC17.valid3
#print axioms N11Formalization.C450Source36GroupedC17.valid4
#print axioms N11Formalization.C450Source36GroupedC17.valid5
#print axioms N11Formalization.C450Source36GroupedC17.valid6
#print axioms N11Formalization.C450Source36GroupedC17.valid7
#print axioms N11Formalization.C450Source36GroupedC17.valid8
#print axioms N11Formalization.C450Source36GroupedC17.valid9
#print axioms N11Formalization.C450Source36GroupedC17.valid10
#print axioms N11Formalization.C450Source36GroupedC17.valid11
#print axioms N11Formalization.C450Source36GroupedC17.valid12
#print axioms N11Formalization.C450Source36GroupedC17.valid13
#print axioms N11Formalization.C450Source36GroupedC17.valid14
#print axioms N11Formalization.C450Source36GroupedC17.bound
#print axioms N11Formalization.C450Source36GroupedC17.endpoint_checks
