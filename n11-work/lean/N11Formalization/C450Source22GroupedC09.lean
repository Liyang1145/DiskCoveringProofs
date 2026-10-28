import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((813515589:ℚ)/1250000000),((3408132513:ℚ)/5000000000),((-2608132513:ℚ)/6200000000),((-4014609123:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5426713241:ℚ)/10000000000),((32367379606353450619284626545597219704027012270272927059:ℚ)/206753765869140625000000000000000000000000000000000000000),((48430285450179212029099049:ℚ)/346560000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((210849361:ℚ)/312500000),((3467883289:ℚ)/5000000000),((-2667883289:ℚ)/6437500000),((-1055945527:ℚ)/3278125000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1195705907:ℚ)/2500000000),((431014493355300138208926688714766334986142055885624287:ℚ)/2834678336310386657714843750000000000000000000000000000),((954681232159546471501883:ℚ)/7220000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((6866664333:ℚ)/10000000000),((881905143:ℚ)/1250000000),((-681905143:ℚ)/1639062500),((-11542216777:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4429097331:ℚ)/10000000000),((5614175138180146655129507361178654910434963995706227187159:ℚ)/36975624050000000000000000000000000000000000000000000000000),((2848684235805366115798390841:ℚ)/22179840000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((436632671:ℚ)/625000000),((3557484379:ℚ)/5000000000),((-2757484379:ℚ)/6675000000),((-2216428697:ℚ)/6734375000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((505855589:ℚ)/1250000000),((149102260323693200789000911476744437927887823481923107:ℚ)/995435686642304062843322753906250000000000000000000000),((3599099281146086707638043:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7045842487:ℚ)/10000000000),((1434938031:ℚ)/2000000000),((-1114938031:ℚ)/2693750000),((-35880897409:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3842374717:ℚ)/10000000000),((258985735265669783675869704634219483594735747726215038371873:ℚ)/1729879786853125000000000000000000000000000000000000000000000),((907213412797332690036173387:ℚ)/7393280000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((22204863:ℚ)/31250000),((7234405499:ℚ)/10000000000),((-5634405499:ℚ)/13587500000),((-37811347:ℚ)/114218750),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3627018973:ℚ)/10000000000),((94679882141756584664924069961207377711380956081481:ℚ)/632705759282410144805908203125000000000000000000000),((72472626823118636201:ℚ)/600000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((1433052783:ℚ)/2000000000),((3647057473:ℚ)/5000000000),((-167473969:ℚ)/403125000),((-1049052783:ℚ)/3160000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1699351911:ℚ)/5000000000),((691371167146624206759357897034463653956707339061643:ℚ)/4622240625000000000000000000000000000000000000000000),((105453751708399565603694641:ℚ)/887193600000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7224965907:ℚ)/10000000000),((7353818649:ℚ)/10000000000),((-5753818649:ℚ)/13825000000),((-37134761349:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((315461141:ℚ)/1000000000),((3202092373426482608847034344625365568065405292241791023453:ℚ)/21417355929907226562500000000000000000000000000000000000000),((2593515205577784392724876281:ℚ)/22179840000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((7284662283:ℚ)/10000000000),((1482703351:ℚ)/2000000000),((-1162703351:ℚ)/2788750000),((-4172515109:ℚ)/12500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((361342769:ℚ)/1250000000),((23847586045923750105388057959071600696646606418979594039:ℚ)/159573554992675781250000000000000000000000000000000000000),((2550566280904461982836357641:ℚ)/22179840000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((7344353189:ℚ)/10000000000),((376644837:ℚ)/500000000),((-296644837:ℚ)/703125000),((-37970472323:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1300538953:ℚ)/5000000000),((6362502133380779990747537807863703019287171875567939837381:ℚ)/42108580800000000000000000000000000000000000000000000000000),((835832316097084927770514083:ℚ)/7393280000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7463719137:ℚ)/10000000000),((7771595493:ℚ)/10000000000),((-6171595493:ℚ)/14300000000),((-12935344653:ℚ)/39400000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1896604399:ℚ)/10000000000),((1053821536793890519557146874745671032249298020936264219557:ℚ)/6833052118750000000000000000000000000000000000000000000000),((6706362324566128957340201:ℚ)/61440000000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((770239119:ℚ)/1000000000),((4005109519:ℚ)/5000000000),((-3205109519:ℚ)/7387500000),((-4047673833:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((515754926417224577905279203090164472342793186904808794569:ℚ)/3353644275000000000000000000000000000000000000000000000000),((53592593:ℚ)/512000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((3970494861:ℚ)/5000000000),((4243633599:ℚ)/5000000000),((-3443633599:ℚ)/7625000000),((-2341496003:ℚ)/7200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3775982783594051825044436526014354243229192042030547963:ℚ)/23716800000000000000000000000000000000000000000000000000),((53592593:ℚ)/512000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8417992313:ℚ)/10000000000),((10393504903:ℚ)/10000000000),((-2931168301:ℚ)/5400000000),((-45485946191:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((64593417912158431573941369014945935139250067647045260405299:ℚ)/345600000000000000000000000000000000000000000000000000000000),((53592593:ℚ)/512000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((2064818287:ℚ)/2000000000),((14200812751:ℚ)/10000000000),((-12600812751:ℚ)/20000000000),((-11765728009:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((43593910304815804141789039178662209771613736151697199909:ℚ)/201835929600000000000000000000000000000000000000000000000),((53592593:ℚ)/512000000)⟩
theorem valid14 : Valid source22 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC09
#check @N11Formalization.C450Source22GroupedC09.bound
#print axioms N11Formalization.C450Source22GroupedC09.valid0
#print axioms N11Formalization.C450Source22GroupedC09.valid1
#print axioms N11Formalization.C450Source22GroupedC09.valid2
#print axioms N11Formalization.C450Source22GroupedC09.valid3
#print axioms N11Formalization.C450Source22GroupedC09.valid4
#print axioms N11Formalization.C450Source22GroupedC09.valid5
#print axioms N11Formalization.C450Source22GroupedC09.valid6
#print axioms N11Formalization.C450Source22GroupedC09.valid7
#print axioms N11Formalization.C450Source22GroupedC09.valid8
#print axioms N11Formalization.C450Source22GroupedC09.valid9
#print axioms N11Formalization.C450Source22GroupedC09.valid10
#print axioms N11Formalization.C450Source22GroupedC09.valid11
#print axioms N11Formalization.C450Source22GroupedC09.valid12
#print axioms N11Formalization.C450Source22GroupedC09.valid13
#print axioms N11Formalization.C450Source22GroupedC09.valid14
#print axioms N11Formalization.C450Source22GroupedC09.bound
#print axioms N11Formalization.C450Source22GroupedC09.endpoint_checks
