import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((99651239:ℚ)/156250000),((3346363591:ℚ)/5000000000),((-1682363591:ℚ)/9920000000),((-32151239:ℚ)/402343750),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((287522041:ℚ)/500000000),((3669774392130173011236831502736845710969499259820019:ℚ)/18928872607648372650146484375000000000000000000000000),((-4990545900496294074159:ℚ)/56406250000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3309127483:ℚ)/5000000000),((6812986109:ℚ)/10000000000),((-3484986109:ℚ)/20600000000),((-1149127483:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2569611499:ℚ)/5000000000),((69227302958701579098761522239758037495889703787651088431:ℚ)/362838827047729492187500000000000000000000000000000000000),((-5944201225727495255536731:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((6738457689:ℚ)/10000000000),((6933190357:ℚ)/10000000000),((-3605190357:ℚ)/20980000000),((-806152563:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4807698279:ℚ)/10000000000),((220524589573747695123508889399590452188960261163954668577:ℚ)/1155488251562500000000000000000000000000000000000000000000),((-25456407017120854452809059:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((1371721561:ℚ)/2000000000),((3496636451:ℚ)/5000000000),((-610878817:ℚ)/3560000000),((-507721561:ℚ)/5387500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4453768221:ℚ)/10000000000),((193136928664637309880558360608491573525813957967864993:ℚ)/1019326143121719360351562500000000000000000000000000000),((-1085757709810460333833059:ℚ)/9241600000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3459332013:ℚ)/5000000000),((3526671431:ℚ)/5000000000),((-1862671431:ℚ)/10775000000),((-1299332013:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((533332539:ℚ)/1250000000),((1280771180546072931190753276813296716229132776519064359313:ℚ)/6757342917395019531250000000000000000000000000000000000000),((-6997673682522205127858251:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((6978708137:ℚ)/10000000000),((7113400571:ℚ)/10000000000),((-3785400571:ℚ)/21740000000),((-2658708137:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((508944011:ℚ)/1250000000),((2211187681517763094613452528835021996228713163387556132023:ℚ)/11662032555093383789062500000000000000000000000000000000000),((-28839440658254950902627651:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7038740461:ℚ)/10000000000),((448340397:ℚ)/625000000),((-240340397:ℚ)/1370625000),((-2718740461:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3867227569:ℚ)/10000000000),((286234321838757907021341922103783205555481363358120997981:ℚ)/1509047211755371093750000000000000000000000000000000000000),((-29690183803325947866461259:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((7098761307:ℚ)/10000000000),((7293503367:ℚ)/10000000000),((-566500481:ℚ)/3160000000),((-926253769:ℚ)/9375000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((730426949:ℚ)/2000000000),((911393507582851633609708590377321723938544805804758407:ℚ)/4767626523971557617187500000000000000000000000000000000),((-30542927286530936277036571:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7218769757:ℚ)/10000000000),((463344767:ℚ)/625000000),((-255344767:ℚ)/1406250000),((-222982289:ℚ)/2200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3180784333:ℚ)/10000000000),((114584372755019017361026808303429510203114473646296739:ℚ)/598950000000000000000000000000000000000000000000000000),((-32254427347045564847889771:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((91734197:ℚ)/125000000),((3826709217:ℚ)/5000000000),((-2162709217:ℚ)/11440000000),((-37734197:ℚ)/369375000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2629663899:ℚ)/10000000000),((7361760165000412127910885025390457178986716397473:ℚ)/37914218521118164062500000000000000000000000000000),((-5308431849344376980811:ℚ)/36100000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((3789274389:ℚ)/5000000000),((3946584409:ℚ)/5000000000),((-2282584409:ℚ)/11820000000),((-1629274389:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((6012103:ℚ)/80000000),((2547378923436970150906851566603971068265967176961914690201:ℚ)/13100172949218750000000000000000000000000000000000000000000),((-9359307661746437953174459:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((3909107863:ℚ)/5000000000),((837226859:ℚ)/1000000000),((-504426859:ℚ)/2440000000),((-1749107863:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((107939916403179131755289218417250932899908154184593831931:ℚ)/540298350000000000000000000000000000000000000000000000000),((-81693:ℚ)/500000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((2074290919:ℚ)/2500000000),((5142368057:ℚ)/5000000000),((-1159456019:ℚ)/4320000000),((-994290919:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((38349909466087906087915519177851478689057415579862253407:ℚ)/168750000000000000000000000000000000000000000000000000000),((-81693:ℚ)/500000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((10209170817:ℚ)/10000000000),((14099313337:ℚ)/10000000000),((-10771313337:ℚ)/32000000000),((-1963056939:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2574839844426725173341326395547318312520088175396435961:ℚ)/9733600000000000000000000000000000000000000000000000000),((-81693:ℚ)/500000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC12
#check @N11Formalization.C450Source28GroupedC12.bound
#print axioms N11Formalization.C450Source28GroupedC12.valid0
#print axioms N11Formalization.C450Source28GroupedC12.valid1
#print axioms N11Formalization.C450Source28GroupedC12.valid2
#print axioms N11Formalization.C450Source28GroupedC12.valid3
#print axioms N11Formalization.C450Source28GroupedC12.valid4
#print axioms N11Formalization.C450Source28GroupedC12.valid5
#print axioms N11Formalization.C450Source28GroupedC12.valid6
#print axioms N11Formalization.C450Source28GroupedC12.valid7
#print axioms N11Formalization.C450Source28GroupedC12.valid8
#print axioms N11Formalization.C450Source28GroupedC12.valid9
#print axioms N11Formalization.C450Source28GroupedC12.valid10
#print axioms N11Formalization.C450Source28GroupedC12.valid11
#print axioms N11Formalization.C450Source28GroupedC12.valid12
#print axioms N11Formalization.C450Source28GroupedC12.valid13
#print axioms N11Formalization.C450Source28GroupedC12.bound
#print axioms N11Formalization.C450Source28GroupedC12.endpoint_checks
